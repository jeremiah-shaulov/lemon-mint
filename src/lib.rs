mod lempar;

use lempar::LemparReader;

use std::mem;
use std::cmp;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::cell::RefCell;
use std::io::{self, BufRead, BufReader};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;
use std::error::Error;
use std::iter::Take;
use std::slice::Iter;
use std::convert::TryFrom;
use std::rc::Rc;
use std::sync::Arc;
use std::fs::File;
use std::borrow::Cow;

fn typename_to_string(value: String) -> String
{	let value_trimmed = value.trim();
	if value_trimmed.is_empty() || value.starts_with('(') && value.ends_with(')') && value[1 .. value.len()-1].trim().is_empty()
	{	String::new()
	}
	else
	{	if value.len() == value_trimmed.len() {value} else {value_trimmed.to_string()}
	}
}

fn is_terminal_name(s: &str) -> bool
{	s.chars().position(|c| c.is_ascii_lowercase()).is_none()
}

#[derive(Debug)]
pub struct LemonMintError
{	pub filename: Arc<String>,
	pub n_line: usize,
	pub message: String,
}
impl LemonMintError
{	pub fn new(filename: &Arc<String>, n_line: usize, message: String) -> Self
	{	Self {filename: Arc::clone(filename), n_line, message}
	}
}
impl fmt::Display for LemonMintError
{	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
	{	let message: &str = if self.message.is_empty() {"Unspecified error"} else {&self.message};
		if self.filename.is_empty()
		{	write!(f, "{}", message)
		}
		else
		{	write!(f, "{}({}): {}", self.filename, self.n_line, message)
		}
	}
}
impl Error for LemonMintError {}

type ParserResult<T> = Result<T, LemonMintError>;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Directive
{	Rule,
	TokenType,
	Type,
	DefaultType,
	StartSymbol,
	Trace,
	ExtraArgument,
	Left,
	Right,
	Nonassoc,
	Fallback,
	Code,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum SymbolType
{	TERMINAL,
	NONTERMINAL
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Associativity
{	LEFT,
	RIGHT,
	NONASSOC,
	UNKNOWN
}

#[derive(Debug)]
struct Set
{	data: Vec<bool>,
}
impl Set
{	pub fn new(size: usize) -> Self
	{	let mut this = Self {data: Vec::new()};
		if size > 0
		{	this.set_size(size);
		}
		this
	}

	pub fn len(&self) -> usize
	{	self.data.len()
	}

	pub fn set_size(&mut self, size: usize)
	{	self.data.clear();
		self.data.resize(size, false);
	}

	pub fn contains(&self, element: usize) -> bool
	{	*self.data.get(element).unwrap_or(&false)
	}

	pub fn add(&mut self, element: usize) -> bool
	{	let rv = self.contains(element);
		if let Some(v) = self.data.get_mut(element)
		{	*v = true;
		}
		!rv
	}

	pub fn intersect(&mut self, other: &Set) -> bool
	{	let mut changed = false;
		for (i, v) in &mut self.data.iter_mut().enumerate()
		{	if !*v && other.contains(i)
			{	changed = true;
				*v = true;
			}
		}
		return changed;
	}
}

/// Terminal or nonterminal symbol from the grammar.
#[derive(Debug)]
struct Symbol
{	name: Rc<String>,              // Name of the symbol
	index: usize,                  // Index number for this symbol
	typ: SymbolType,               // Symbols are all either TERMINALS or NTs
	sym_rules_arr: Vec<usize>,     // Array of rules of this (if an NT) (indices in rules array)
	fallback: Option<Rc<RefCell<Symbol>>>, // fallback token in case this token doesn't parse
	prec: i32,                     // Precedence if defined (-1 otherwise)
	assoc: Associativity,          // Associativity if precedence is defined
	firstset: Set,                 // First-set for all rules of this symbol
	lambda: bool,                  // True if NT and can generate an empty string
	data_type: String,             // The data type of information held by this object. Only used if type==NONTERMINAL
	dtnum: usize,                  // The data type number. In the parser, the value stack is a union. The .Symbol%d element of this union is the correct data type for this object
}
impl Symbol
{	fn new(name: &str, index: usize) -> Self
	{	let typ = if is_terminal_name(name) || name=="$" {SymbolType::TERMINAL} else {SymbolType::NONTERMINAL};
		Self
		{	name: Rc::new(String::new()),
			index,
			typ,
			sym_rules_arr: Vec::new(),
			fallback: None,
			prec: -1,
			assoc: Associativity::UNKNOWN,
			firstset: Set::new(0),
			lambda: false,
			data_type: String::new(),
			dtnum: 0,
		}
	}
}
impl PartialEq for Symbol
{	fn eq(&self, other: &Self) -> bool
	{	self.index == other.index
	}
}

/// Each production rule in the grammar is stored in this structure.
#[derive(Debug)]
struct Rule
{	rule_filename: Arc<String>,
	rule_n_line: usize,            // Line number for the rule
	lhs: Rc<RefCell<Symbol>>,      // Left-hand side of the rule
	lhs_start: bool,               // True if left-hand side is the start symbol
	rhs: Vec<Rc<RefCell<Symbol>>>, // The RHS symbols
	rhs_aliases: Vec<String>,      // An alias for each RHS symbol (NULL if none)
	line: usize,                   // Line number at which code begins
	code: String,                  // The code executed when this rule is reduced
	precsym: Option<Rc<RefCell<Symbol>>>, // Precedence symbol for this rule
	index: usize,                  // An index number for this rule
	can_reduce: bool,              // True if this rule is ever reduced
	does_reduce: bool,             // Reduce actions occur after optimization
}
impl Rule
{	fn new(rule_filename: &Arc<String>, rule_n_line: usize, lhs: &Rc<RefCell<Symbol>>, index: usize, code: String) -> Self
	{	Self
		{	rule_filename: Arc::clone(rule_filename),
			rule_n_line,
			lhs: Rc::clone(lhs),
			lhs_start: false,
			rhs: Vec::new(),
			rhs_aliases: Vec::new(),
			line: 0,
			code,
			precsym: None,
			index,
			can_reduce: false,
			does_reduce: false,
		}
	}
}
impl fmt::Display for Rule
{	/// Write text on "out" that describes the rule
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
	{	write!(f, "{} ::=", self.lhs.borrow().name)?;
		for sp in self.rhs.iter()
		{	write!(f, " {}", sp.borrow().name)?;
		}
		Ok(())
	}
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
struct ConfigKey
{	n_rule: usize,
	dot: usize,
}
impl ConfigKey
{	fn new(config: &Config) -> Self
	{	Self
		{	n_rule: config.n_rule,
			dot: config.dot,
		}
	}
}
impl cmp::Ord for ConfigKey
{	fn cmp(&self, other: &Self) -> cmp::Ordering
	{	let mut res = self.n_rule.cmp(&other.n_rule);
		if res == Ordering::Equal
		{	res = self.dot.cmp(&other.dot);
		}
		res
	}
}
impl cmp::PartialOrd for ConfigKey
{	fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering>
	{	Some(self.cmp(other))
	}
}

/// A configuration is a production rule of the grammar together with
/// a mark (dot) showing how much of that rule has been processed so far.
/// Configurations also contain a follow-set which is a list of terminal
/// symbols which are allowed to immediately follow the end of the rule.
/// Every configuration is recorded as an instance of this structure.
#[derive(Debug)]
struct Config
{	n_rule: usize,                  // The rule upon which the configuration is based
	dot: usize,                     // The parse point
	fws: Set,                       // Follow-set for this configuration only
	fplp: Vec<Rc<RefCell<Config>>>, // Follow-set forward propagation links
	bplp: Vec<Rc<RefCell<Config>>>, // Follow-set backwards propagation links
	n_state: usize,                 // Pointer to state which contains this
	status_is_complete: bool,       // used during followset and shift computations
}
impl Config
{	pub fn new(n_rule: usize, dot: usize, fws_size: usize) -> Self
	{	Self
		{	n_rule,
			dot,
			fws: Set::new(fws_size),
			fplp: Vec::new(),
			bplp: Vec::new(),
			n_state: std::usize::MAX,
			status_is_complete: false,
		}
	}
}
impl cmp::Ord for Config
{	fn cmp(&self, other: &Self) -> cmp::Ordering
	{	ConfigKey::new(self).cmp(&ConfigKey::new(other))
	}
}
impl cmp::PartialOrd for Config
{	fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering>
	{	Some(self.cmp(other))
	}
}
impl cmp::PartialEq for Config
{	fn eq(&self, other: &Self) -> bool
	{	ConfigKey::new(self).eq(&ConfigKey::new(other))
	}
}
impl Eq for Config {}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
enum ActionType
{	Shift,
	Accept,
	Reduce,
	Error,
	SsConflict,  // A shift/shift conflict
	SrConflict,  // Was a reduce, but part of a conflict
	RrConflict,  // Was a reduce, but part of a conflict
	ShResolved, // Was a shift.  Precedence resolved conflict
	RdResolved, // Was reduce.  Precedence resolved conflict
	NotUsed,    // Deleted by compression
	ShiftReduce // Shift first, then reduce
}

#[derive(Debug, PartialEq, Copy, Clone)]
enum StateOrRule
{	State(usize), // n_state: usize - The new state, if a shift
	Rule(usize),  // The rule, if a reduce
	EmptyRule     // Empty reduce rule for "accepting" token
}

/// Every shift or reduce operation is stored as one of this structure.
#[derive(Debug)]
struct Action
{	id: i32,
	sp: Rc<RefCell<Symbol>>,              // The look-ahead symbol
	typ: ActionType,
	x: StateOrRule,
	sp_opt: Option<Rc<RefCell<Symbol>>>, // ActionType::ShiftReduce optimization to this symbol
}
impl Action
{	fn new_state(id: i32, sp: &Rc<RefCell<Symbol>>, n_state: usize) -> Action
	{	Action
		{	id,
			sp: Rc::clone(sp),
			typ: ActionType::Shift,
			x: StateOrRule::State(n_state),
			sp_opt: None,
		}
	}

	fn new_rule(id: i32, symbol: &Rc<RefCell<Symbol>>, typ: ActionType, n_rule: usize) -> Action
	{	Action
		{	id,
			sp: Rc::clone(symbol),
			typ,
			x: StateOrRule::Rule(n_rule),
			sp_opt: None,
		}
	}

	fn new_empty_rule(id: i32, symbol: &Rc<RefCell<Symbol>>, typ: ActionType) -> Action
	{	Action
		{	id,
			sp: Rc::clone(symbol),
			typ,
			x: StateOrRule::EmptyRule,
			sp_opt: None,
		}
	}
}
impl cmp::Ord for Action
{	fn cmp(&self, other: &Self) -> cmp::Ordering
	{	let index = self.sp.borrow().index;
		let other_index = other.sp.borrow().index;
		let mut res = index.cmp(&other_index);
		if res == Ordering::Equal
		{	res = self.typ.cmp(&other.typ);
			if res == Ordering::Equal
			{	if self.typ==ActionType::Reduce || self.typ==ActionType::ShiftReduce
				{	if let StateOrRule::Rule(n_rule) = self.x
					{	if let StateOrRule::Rule(other_n_rule) = other.x
						{	if n_rule < other_n_rule
							{	return Ordering::Less;
							}
							if n_rule > other_n_rule
							{	return Ordering::Greater;
							}
						}
					}
				}
				res = self.id.cmp(&other.id);
			}
		}
		res
	}
}
impl cmp::PartialOrd for Action
{	fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering>
	{	Some(self.cmp(other))
	}
}
impl cmp::PartialEq for Action
{	fn eq(&self, other: &Self) -> bool
	{	self.cmp(other) == Ordering::Equal
	}
}
impl Eq for Action {}

/// Each state of the generated parser's finite state machine is encoded as an instance of this structure.
#[derive(Debug)]
struct State
{	basis: Vec<Rc<RefCell<Config>>>,          // The basis configurations for this state
	configurations: Vec<Rc<RefCell<Config>>>, // All configurations in this set
	n_state: usize,                    // Sequential number for this state
	actions: Vec<Rc<RefCell<Action>>>, // Array of actions for this state
	n_token_act: usize,
	n_nt_act: usize,                   // Number of actions on terminals and nonterminals
	token_offset: isize,
	nt_offset: isize,                  // yy_action[] offset for terminals and nonterms
	default_reduce_action: usize,      // Default action is to REDUCE by this rule
	default_reduce_rule: usize,        // The default REDUCE rule
	auto_reduce: bool,
}
impl State
{	pub fn new(n_state: usize, basis: Vec<Rc<RefCell<Config>>>, configurations: Vec<Rc<RefCell<Config>>>) -> Self
	{	Self
		{	basis,
			configurations,
			n_state,
			actions: Vec::new(),
			n_token_act: 0,
			n_nt_act: 0,
			token_offset: 0,
			nt_offset: 0,
			default_reduce_action: 0,
			default_reduce_rule: std::usize::MAX,
			auto_reduce: false,
		}
	}
}

/// Each state contains a set of token transaction and a set of
/// nonterminal transactions.  Each of these sets makes an instance
/// of the following structure.  An array of these structures is used
/// to order the creation of entries in the `yy_action[]` table.
#[derive(Debug)]
struct AxSet
{	n_state: usize, // Index in sorted states array
	is_tkn: bool,    // True to use tokens.  False for non-terminals
	n_action: usize,   // Number of actions
	i_order: usize,    // Original order of action sets
}
impl AxSet
{	fn new(n_state: usize, is_tkn: bool, n_action: usize, i_order: usize) -> Self
	{	Self
		{	n_state,
			is_tkn,
			n_action,
			i_order,
		}
	}
}
impl cmp::Ord for AxSet
{	fn cmp(&self, other: &Self) -> cmp::Ordering
	{	let mut res = other.n_action.cmp(&self.n_action); // descending order
		if res == Ordering::Equal
		{	res = self.i_order.cmp(&other.i_order);
		}
		res
	}
}
impl cmp::PartialOrd for AxSet
{	fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering>
	{	Some(self.cmp(other))
	}
}
impl cmp::PartialEq for AxSet
{	fn eq(&self, other: &Self) -> bool
	{	self.cmp(other) == Ordering::Equal
	}
}
impl Eq for AxSet {}

/// The state of the yy_action table under construction is an instance of
/// the following structure.
///
/// The yy_action table maps the pair (state_number, lookahead) into an
/// action_number.  The table is an array of integers pairs.  The state_number
/// determines an initial offset into the yy_action array.  The lookahead
/// value is then added to this initial offset to get an index X into the
/// yy_action array. If the `aAction[X]`.lookahead equals the value of the
/// of the lookahead input, then the value of the action_number output is
/// `aAction[X].action`.  If the lookaheads do not match then the
/// default action for the state_number is returned.
///
/// All actions associated with a single state_number are first entered
/// into `aLookahead[]` using multiple calls to acttab_action().  Then the
/// actions for that single state_number are placed into the `aAction[]`
/// array with a single call to acttab_insert().  The acttab_insert() call
/// also resets the `aLookahead[]` array in preparation for the next
/// state number.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct LookaheadAction
{	lookahead: usize, // Value of the lookahead token
	action: usize,    // Action to take on the given lookahead
}
impl LookaheadAction
{	fn new(lookahead: usize, action: usize) -> Self
	{	Self
		{	lookahead,
			action,
		}
	}
}

#[derive(Debug)]
struct ActTab
{	n_action: usize,                   // Number of used slots in aAction[]
	a_action: Vec<LookaheadAction>,    // The yy_action[] table under construction
	a_lookahead: Vec<LookaheadAction>, // A single new transaction set
	min_lookahead: usize,              // Minimum aLookahead[].lookahead
	max_lookahead: usize,              // Maximum aLookahead[].lookahead
	min_action: usize,                 // Action associated with mnLookahead

	n_terminals: usize,                // Number of terminal symbols
	n_symbols: usize,                  // Total number of symbols

	min_token_offset: isize,
	max_token_offset: isize,
	min_nt_offset: isize,
	max_nt_offset: isize,

	n_fallbacks: usize,
	n_shift_offset: usize,
	reduce_count: usize,
}
impl ActTab
{	fn new(n_terminals: usize, n_symbols: usize) -> Self
	{	Self
		{	n_action: 0,
			a_action: Vec::new(),
			a_lookahead: Vec::new(),
			min_lookahead: 0,
			max_lookahead: 0,
			min_action: 0,

			n_terminals,
			n_symbols,

			min_token_offset: 0,
			max_token_offset: 0,
			min_nt_offset: 0,
			max_nt_offset: 0,

			n_fallbacks: 0,
			n_shift_offset: 0,
			reduce_count: 0,
		}
	}

	fn get_n_lookahead(&self) -> usize
	{	self.n_action
	}

	fn get_n_actions(&self) -> usize
	{	let mut n_action = self.n_action;
		for rec in  self.a_action.iter().take(n_action).rev()
		{	if rec.lookahead == std::usize::MAX
			{	n_action -= 1;
			}
			else
			{	break;
			}
		}
		n_action
	}

	fn iter(&self) -> Take<Iter<LookaheadAction>>
	{	self.a_action.iter().take(self.n_action)
	}

	/// Add a new action to the current transaction set.
	/// This routine is called once for each lookahead for a particular state.
	fn acttab_action(&mut self, lookahead: usize, action: usize)
	{	if self.a_lookahead.len() == 0
		{	self.max_lookahead = lookahead;
			self.min_lookahead = lookahead;
			self.min_action = action;
		}
		else
		{	if self.max_lookahead < lookahead
			{	self.max_lookahead = lookahead;
			}
			if self.min_lookahead > lookahead
			{	self.min_lookahead = lookahead;
				self.min_action = action;
			}
		}
		self.a_lookahead.push(LookaheadAction::new(lookahead, action));
	}

	/// Add the transaction set built up with prior calls to acttab_action() into the current action table.
	/// Then reset the transaction set back to an empty set in preparation for a new round of acttab_action() calls.
	///
	/// Return the offset into the action table of the new transaction.
	fn acttab_insert(&mut self, make_it_safe: bool) -> isize
	{	assert!(self.a_lookahead.len() > 0);

		// Make sure we have enough space to hold the expanded action table in the worst case.  The worst case occurs if the transaction set
		// must be appended to the current action table
		if self.n_action + self.n_symbols + 1 >= self.a_action.len()
		{	self.a_action.resize(self.n_action + self.n_symbols + self.a_action.len() + 21, LookaheadAction::new(std::usize::MAX, std::usize::MAX));
		}

		// Scan the existing action table looking for an offset that is a duplicate of the current transaction set.  Fall out of the loop
		// if and when the duplicate is found.
		//
		// i is the index in aAction[] where mnLookahead is inserted.
		let mut found_offset = std::usize::MAX;
		let end = if make_it_safe {self.min_lookahead} else {0};
'l:		for i in (end .. self.n_action).rev()
		{	if self.a_action[i].lookahead == self.min_lookahead
			{	// All lookaheads and actions in the aLookahead[] transaction must match against the candidate aAction[i] entry.
				if self.a_action[i].action == self.min_action
				{	for j in 0..self.a_lookahead.len()
					{	let k = self.a_lookahead[j].lookahead + i - self.min_lookahead;
						if k>=self.n_action || self.a_lookahead[j].lookahead != self.a_action[k].lookahead || self.a_lookahead[j].action != self.a_action[k].action
						{	continue 'l;
						}
					}
					// No possible lookahead value that is not in the aLookahead[] transaction is allowed to match aAction[i]
					let mut n = 0;
					for j in 0..self.n_action
					{	if self.a_action[j].lookahead != std::usize::MAX
						{	if self.a_action[j].lookahead == (j + self.min_lookahead).wrapping_sub(i)
							{	n += 1;
							}
						}
					}
					if n == self.a_lookahead.len()
					{	found_offset = i;  // An exact match is found at offset i
						break;
					}
				}
			}
		}

		// If no existing offsets exactly match the current transaction, find an an empty offset in the aAction[] table in which we can add the aLookahead[] transaction.
		if found_offset == std::usize::MAX
		{	// Look for holes in the aAction[] table that fit the current aLookahead[] transaction.  Leave found_offset set to the offset of the hole.
			// If no holes are found, found_offset is left at nAction, which means the transaction will be appended.
			found_offset = if make_it_safe {self.min_lookahead} else {0};
'm:			for i in found_offset .. self.a_action.len() - self.max_lookahead
			{	if self.a_action[i].lookahead == std::usize::MAX
				{	for j in 0 .. self.a_lookahead.len()
					{	let k = self.a_lookahead[j].lookahead + i - self.min_lookahead;
						if k >= self.a_action.len() || self.a_action[k].lookahead != std::usize::MAX
						{	continue 'm;
						}
					}
					for j in 0 .. self.n_action
					{	if self.a_action[j].lookahead == (j + self.min_lookahead).wrapping_sub(i)
						{	continue 'm;
						}
					}
					found_offset = i; // Fits in empty slots
					break;
				}
			}
		}

		// Insert transaction set at index found_offset
		for j in 0 .. self.a_lookahead.len()
		{	let k = self.a_lookahead[j].lookahead - self.min_lookahead + found_offset;
			self.a_action[k] = self.a_lookahead[j];
			if k >= self.n_action
			{	self.n_action = k + 1;
			}
		}
		if make_it_safe && found_offset+self.n_terminals >= self.n_action
		{	self.n_action = found_offset+self.n_terminals+1;
		}
		self.a_lookahead.clear();

		// Return the offset that is added to the lookahead in order to get the index into yy_action of the action
		return found_offset as isize - self.min_lookahead as isize;
	}
}

#[derive(Debug)]
struct SymbolsBuilder
{	symbols_map: HashMap<Rc<String>, Rc<RefCell<Symbol>>>,
	n_terminals: usize,
	n_nonterminals: usize,
}
impl SymbolsBuilder
{	pub fn new(empty: bool) -> Self
	{	let mut this = Self
		{	symbols_map: HashMap::new(),
			n_terminals: 0,
			n_nonterminals: 0,
		};
		if !empty
		{	this.add(Rc::new("$".to_string()));
		}
		this
	}

	/// Return a pointer to the (terminal or nonterminal) symbol "symbol_name". Create a new symbol if this is the first time "x" has been seen.
	pub fn add(&mut self, symbol_name: Rc<String>) -> Rc<RefCell<Symbol>>
	{	if let Some(symbol) = self.symbols_map.get(&symbol_name)
		{	let symbol = Rc::clone(symbol);
			return symbol;
		}
		let index = if is_terminal_name(symbol_name.as_ref()) || symbol_name.as_ref()=="$"
		{	self.n_terminals += 1;
			self.n_terminals - 1
		}
		else
		{	self.n_nonterminals += 1;
			self.n_nonterminals - 1
		};
		let symbol = Rc::new(RefCell::new(Symbol::new(&symbol_name, index))); // need to set the name later in into_symbols()
		self.symbols_map.insert(symbol_name, Rc::clone(&symbol));
		symbol
	}

	/// Return an array of pointers to all data in the table.
	/// The array is obtained from malloc.  Return NULL if memory allocation problems, or if the array is empty.
	pub fn into_symbols(mut self, start_name: &String, nonterminal_types: HashMap<String, StringInFile>, precedence: HashMap<String, PrecedenceInFile>) -> ParserResult<Symbols>
	{	// nonterminal_types
		for (symbol_name, symbol_type) in nonterminal_types
		{	if let Some(symbol) = self.symbols_map.get(&symbol_name)
			{	symbol.borrow_mut().data_type = symbol_type.string;
			}
			else
			{	return Err(LemonMintError::new(&symbol_type.filename, symbol_type.n_line, format!("No such nonterminal symbol when defining symbol type: \"{}\"", symbol_name)));
			}
		}
		// precedence
		for (symbol_name, precedence) in precedence
		{	if let Some(symbol) = self.symbols_map.get(&symbol_name)
			{	let mut symbol = symbol.borrow_mut();
				symbol.prec = precedence.precedence;
				symbol.assoc = precedence.assoc;
			}
			else
			{	return Err(LemonMintError::new(&precedence.filename, precedence.n_line, format!("No such terminal symbol \"{}\" when defining precedence", symbol_name)));
			}
		}
		// into Symbols
		let n_symbols = self.symbols_map.len();
		let default_symbol = self.add(Rc::new("{default}".to_string()));
		let default_symbol_index = default_symbol.borrow().index + self.n_terminals;
		let mut start_symbol_index = std::usize::MAX;
		let mut error_symbol_index = std::usize::MAX;
		let mut array = Vec::new();
		let empty = Rc::new(RefCell::new(Symbol::new("", 0)));
		array.resize_with(self.symbols_map.len(), || empty.clone());
		for (symbol_name, symbol) in self.symbols_map
		{	let index =
			{	let mut symbol_mut = symbol.borrow_mut();
				if symbol_mut.typ == SymbolType::NONTERMINAL
				{	symbol_mut.index += self.n_terminals;
				}
				if *symbol_name == *start_name
				{	start_symbol_index = symbol_mut.index;
				}
				else if symbol_name.as_ref() == "error"
				{	error_symbol_index = symbol_mut.index;
				}
				symbol_mut.name = symbol_name;
				symbol_mut.index
			};
			array[index] = symbol;
		}
		array[0].borrow_mut().typ = SymbolType::NONTERMINAL; // like in lemon
		Ok(Symbols {array, n_symbols, n_terminals: self.n_terminals, default_symbol_index, start_symbol_index, error_symbol_index})
	}
}

#[derive(Debug)]
struct Symbols
{	pub array: Vec<Rc<RefCell<Symbol>>>, // Sorted array of all symbols
	pub n_symbols: usize,                // Number of terminal and nonterminal symbols
	pub n_terminals: usize,              // Number of terminal symbols
	start_symbol_index: usize,
	default_symbol_index: usize,
	error_symbol_index: usize,
}
impl Symbols
{	pub fn get_start_symbol(&self) -> &Rc<RefCell<Symbol>>
	{	&self.array[self.start_symbol_index]
	}

	pub fn get_default_symbol(&self) -> &Rc<RefCell<Symbol>>
	{	&self.array[self.default_symbol_index]
	}

	pub fn get_error_symbol(&self) -> Option<&Rc<RefCell<Symbol>>>
	{	self.array.get(self.error_symbol_index)
	}
}

#[derive(Debug)]
struct States
{	pub array: Vec<State>,
	pub n_no_tail: usize, // Number of states with tail degenerate states removed
}

#[derive(Debug)]
struct StatesBuilder;
impl StatesBuilder
{	/// Compute all LR(0) states for the grammar. Links are added to between some states so that the LR(1) follow sets can be computed later.
	pub fn build(rules: &mut Vec<Rule>, start: &Rc<RefCell<Symbol>>, n_terminals: usize, actions_enum: &mut i32) -> ParserResult<States>
	{	let mut configs_basis_keys_arr = Vec::new();
		let mut configs_basis_arr = Vec::new();
		let mut configs_arr = Vec::new();
		let mut configs_map = HashMap::new();
		let mut states_map = HashMap::new();

		// The basis configuration set for the first state is all rules which have the start symbol as their left-hand side
		for n_rule in start.borrow().sym_rules_arr.iter()
		{	rules[*n_rule].lhs_start = true;
			Self::configlist_add(rules, &mut configs_basis_keys_arr, &mut configs_basis_arr, &mut configs_arr, &mut configs_map, n_terminals, *n_rule, 0, true).borrow_mut().fws.add(0);
		}

		// Compute the first state. All other states will be computed automatically during the computation of the first one.
		// The returned pointer to the first state is not used.
		Self::getstate(rules, &mut configs_basis_keys_arr, &mut configs_basis_arr, &mut configs_arr, &mut configs_map, &mut states_map, n_terminals, actions_enum)?;

		let mut states = States {array: Vec::with_capacity(states_map.len()), n_no_tail: 0}; // Table of states sorted by state number
		for (_, elem) in states_map
		{	states.array.push(Rc::try_unwrap(elem).unwrap().into_inner());
		}
		states.array.sort_by(|a, b| a.n_state.cmp(&b.n_state));
		states.n_no_tail = states.array.len();
		Ok(states)
	}

	/// Return a pointer to a state which is described by the configuration list which has been built from calls to configlist_add.
	fn getstate
	(	rules: &Vec<Rule>,
		configs_basis_keys_arr: &mut Vec<ConfigKey>,
		configs_basis_arr: &mut Vec<Rc<RefCell<Config>>>,
		configs_arr: &mut Vec<Rc<RefCell<Config>>>,
		configs_map: &mut HashMap<ConfigKey, Rc<RefCell<Config>>>,
		states_map: &mut HashMap<Vec<ConfigKey>, Rc<RefCell<State>>>,
		n_terminals: usize,
		actions_enum: &mut i32,
	) -> ParserResult<usize>
	{	// Extract the sorted basis of the new state.  The basis was constructed by prior calls to "configlist_add(*, *, *, true)".
		let mut basis_keys = mem::replace(configs_basis_keys_arr, Vec::new());
		let mut basis = mem::replace(configs_basis_arr, Vec::new());
		basis_keys.sort();
		basis.sort();

		// Find a state with the same basis
		if let Some(found) = states_map.get(&basis_keys)
		{	let found = found.borrow();
			let n_state = found.n_state;
			// A state with the same basis already exists!  Copy all the follow-set propagation links from the state under construction into the
			// preexisting state, then return a pointer to the preexisting state
			for (i, x) in basis.iter().enumerate()
			{	let mut y = found.basis[i].borrow_mut();
				if let Ok(mut x) = x.try_borrow_mut()
				{	mem::swap(&mut x.bplp, &mut y.bplp);
					y.bplp.reserve(x.bplp.len());
					for config in x.bplp.iter()
					{	y.bplp.push(Rc::clone(config));
					}
				}
				else
				{	// assume x and y are the same object
					let len = y.bplp.len();
					y.bplp.reserve(len);
					for i in 0 .. len
					{	let o = Rc::clone(&y.bplp[i]);
						y.bplp.push(o);
					}
				}
			}
			configs_arr.clear();
			Ok(n_state)
		}
		else
		{	// This really is a new state.  Construct all the details
			Self::configlist_closure(rules, configs_basis_keys_arr, configs_basis_arr, configs_arr, configs_map, n_terminals)?; // Compute the configuration closure
			let n_state = states_map.len();
			let mut configurations = mem::replace(configs_arr, Vec::new());
			configurations.sort(); // Sort the configuration closure
			let stp = State::new // A new state structure
			(	n_state, // Every state gets a sequence number
				basis, // Remember the configuration basis
				configurations // Remember the configuration closure
			);
			let stp = Rc::new(RefCell::new(stp));
			states_map.insert(basis_keys, Rc::clone(&stp)); // Add to the state table
			let actions = Self::buildshifts(rules, configs_basis_keys_arr, configs_basis_arr, configs_arr, configs_map, states_map, n_terminals, actions_enum, &stp)?; // Recursively compute successor states
			stp.borrow_mut().actions = actions;
			Ok(n_state)
		}
	}

	/// Construct all successor states to the given state.  A "successor" state is any state which can be reached by a shift action.
	fn buildshifts
	(	rules: &Vec<Rule>,
		configs_basis_keys_arr: &mut Vec<ConfigKey>,
		configs_basis_arr: &mut Vec<Rc<RefCell<Config>>>,
		configs_arr: &mut Vec<Rc<RefCell<Config>>>,
		configs_map: &mut HashMap<ConfigKey, Rc<RefCell<Config>>>,
		states_map: &mut HashMap<Vec<ConfigKey>, Rc<RefCell<State>>>,
		n_terminals: usize,
		actions_enum: &mut i32,
		stp: &Rc<RefCell<State>>
	) -> ParserResult<Vec<Rc<RefCell<Action>>>>
	{	let mut actions = Vec::new();

		// Each configuration becomes complete after it contibutes to a successor state.  Initially, all configurations are incomplete
		for cfp in stp.borrow().configurations.iter()
		{	cfp.borrow_mut().status_is_complete = false;
		}

		// Loop through all configurations of the state "stp"
		for (i, cfp) in stp.borrow().configurations.iter().enumerate()
		{	let (status_is_complete, dot, n_rule) =
			{	let cfp = cfp.borrow();
				(cfp.status_is_complete, cfp.dot, cfp.n_rule)
			};
			if !status_is_complete && dot<rules[n_rule].rhs.len() // !Already used by inner loop && !Can't shift this config
			{	configs_basis_keys_arr.clear();
				configs_basis_arr.clear();
				configs_arr.clear();
				configs_map.clear();
				let sp = Rc::clone(&rules[n_rule].rhs[dot]); // Symbol following the dot in configuration "cfp"

				// For every configuration in the state "stp" which has the symbol "sp" following its dot, add the same configuration to the basis set under
				// construction but with the dot shifted one symbol to the right.
				for bcfp in stp.borrow().configurations.iter().skip(i)
				{	if !bcfp.borrow().status_is_complete && bcfp.borrow().dot<rules[bcfp.borrow().n_rule].rhs.len() // !Already used && !Can't shift this one
					{	let bsp = Rc::clone(&rules[bcfp.borrow().n_rule].rhs[bcfp.borrow().dot]); // Symbol following the dot in configuration "bcfp"
						if *bsp.borrow() == *sp.borrow() // Must be same as for "cfp"
						{	bcfp.borrow_mut().status_is_complete = true; // Mark this config as used
							let newcfg = Self::configlist_add(rules, configs_basis_keys_arr, configs_basis_arr, configs_arr, configs_map, n_terminals, bcfp.borrow().n_rule, bcfp.borrow().dot+1, true);
							newcfg.borrow_mut().bplp.push(Rc::clone(bcfp));
						}
					}
				}

				// Get a pointer to the state described by the basis configuration set constructed in the preceding loop
				let n_state = Self::getstate(rules, configs_basis_keys_arr, configs_basis_arr, configs_arr, configs_map, states_map, n_terminals, actions_enum)?; // A pointer to a successor state

				// The state "newstp" is reached from the state "stp" by a shift action on the symbol "sp"
				actions.insert(0, Rc::new(RefCell::new(Action::new_state(*actions_enum, &sp, n_state)))); // TODO: maybe push(), not insert()
				*actions_enum += 1;
			}
		}
		Ok(actions)
	}

	/// Add another configuration to the configuration list.
	/// dot - Index into the RHS of the rule where the dot goes
	fn configlist_add
	(	rules: &Vec<Rule>,
		configs_basis_keys_arr: &mut Vec<ConfigKey>,
		configs_basis_arr: &mut Vec<Rc<RefCell<Config>>>,
		configs_arr: &mut Vec<Rc<RefCell<Config>>>,
		configs_map: &mut HashMap<ConfigKey, Rc<RefCell<Config>>>,
		n_terminals: usize,
		n_rule: usize,
		dot: usize,
		is_basis: bool
	) -> Rc<RefCell<Config>>
	{	let key = ConfigKey {n_rule: rules[n_rule].index, dot};

		if let Some(found) = configs_map.get(&key)
		{	Rc::clone(found)
		}
		else
		{	let cfp =  Rc::new(RefCell::new(Config::new(n_rule, dot, n_terminals+1)));
			configs_arr.push(Rc::clone(&cfp));
			let key = ConfigKey::new(&cfp.borrow());
			if is_basis
			{	configs_basis_keys_arr.push(key);
				configs_basis_arr.push(Rc::clone(&cfp));
			}
			configs_map.insert(key, Rc::clone(&cfp));
			cfp
		}
	}

	/// Compute the closure of the configuration list
	fn configlist_closure
	(	rules: &Vec<Rule>,
		configs_basis_keys_arr: &mut Vec<ConfigKey>,
		configs_basis_arr: &mut Vec<Rc<RefCell<Config>>>,
		configs_arr: &mut Vec<Rc<RefCell<Config>>>,
		configs_map: &mut HashMap<ConfigKey, Rc<RefCell<Config>>>,
		n_terminals: usize
	) -> ParserResult<()>
	{	let mut c = 0;
		while c < configs_arr.len() // size of configs_arr increases during this loop
		{	let (rule, dot) =
			{	let config = configs_arr[c].borrow();
				(&rules[config.n_rule], config.dot)
			};
			if dot < rule.rhs.len()
			{	let sp = &rule.rhs[dot];
				if sp.borrow().typ == SymbolType::NONTERMINAL
				{	if sp.borrow().sym_rules_arr.is_empty() && sp.borrow().name.as_ref()!="error"
					{	return Err(LemonMintError::new(&rule.rule_filename, rule.line, format!("Nonterminal \"{}\" has no rules.", &sp.borrow().name)));
					}
					for new_n_rule in sp.borrow().sym_rules_arr.iter()
					{	let newcfp = Self::configlist_add(rules, configs_basis_keys_arr, configs_basis_arr, configs_arr, configs_map, n_terminals, *new_n_rule, 0, false);
						let mut found = false;
						for i in dot+1 .. rule.rhs.len()
						{	let xsp = &rule.rhs[i];
							if xsp.borrow().typ == SymbolType::TERMINAL
							{	newcfp.borrow_mut().fws.add(xsp.borrow().index);
								found = true;
								break;
							}
							newcfp.borrow_mut().fws.intersect(&xsp.borrow().firstset);
							if !xsp.borrow().lambda
							{	found = true;
								break;
							}
						}
						if !found
						{	configs_arr[c].borrow_mut().fplp.insert(0, newcfp); // TODO: maybe push(), not insert()
						}
					}
				}
			}
			c += 1;
		}
		Ok(())
	}
}

#[derive(Debug)]
struct StringInFile
{	filename: Arc<String>,
	n_line: usize,
	string: String,
}

#[derive(Debug)]
struct PrecedenceInFile
{	filename: Arc<String>,
	n_line: usize,
	assoc: Associativity,
	precedence: i32,
}

struct ArrayFormatter
{	i: usize,
	values_on_line: usize,
	endl: &'static str,
}
impl ArrayFormatter
{	pub fn new(values_on_line: usize) -> Self
	{	Self
		{	i: 0,
			values_on_line,
			endl: "\n[\t",
		}
	}

	pub fn separ<W>(&mut self, out: &mut W) -> io::Result<()> where W: io::Write
	{	if self.i % self.values_on_line == 0
		{	write!(out, "{}/* {:5} */  ", self.endl, self.i)?;
			self.endl = ",\n\t";
		}
		else
		{	write!(out, ", ")?;
		}
		self.i += 1;
		Ok(())
	}

	pub fn end<W>(self, out: &mut W) -> io::Result<()> where W: io::Write
	{	writeln!(out, "{}];", if self.i==0 {" ["} else {"\n"})
	}
}

/// Builder class that will finally generate `LemonMint`. Call builder methods to supply parser rules and options - everything that you would normally put to Lemon's Y-grammar file.
/// Or you can feed the Y-file itself (it's syntax is similar to Lemon's one).
///
/// # Example
///
/// ```
/// use lemon_mint::LemonMintBuilder;
/// use std::sync::Arc;
///
/// let fake_filename = Arc::new("source.y".to_string()); // will appear in error messages
/// let builder = LemonMintBuilder::new().load_y(&fake_filename, "%token_type {f64}\nUnit ::= NEW_LINE.".as_bytes()).unwrap();
/// let lemon = builder.try_into_lemon().unwrap();
/// ```
///
/// Or:
///
/// ```
/// use lemon_mint::LemonMintBuilder;
/// use std::sync::Arc;
///
/// let fake_filename = Arc::new("source.y".to_string()); // will appear in error messages
/// let builder = LemonMintBuilder::new()
/// 	.set_token_type("f64".to_string()).unwrap()
/// 	.add_rule(&fake_filename, 1, "Unit".to_string(), "NEW_LINE", "".to_string()).unwrap();
/// let lemon = builder.try_into_lemon().unwrap();
/// ```
#[derive(Debug)]
pub struct LemonMintBuilder
{	rules: Vec<Rule>,                  // All rules
	token_type: String,                // Type of terminal symbols in the parser stack
	vartype: String,                   // The default type of non-terminal symbols
	start_name: String,                // Name of the start symbol for the grammar
	with_trace: bool,
	trace_prompt: String,              // Prompt to preface each trace message, if with_trace is true
	extracode: String,                 // Code appended to the generated file
	n_conflicts: usize,                // Number of parsing conflicts
	n_action_table_entries: usize,     // Number of entries in the yy_action[] table
	tables_size: usize,                // Total table size of all tables in bytes
	has_fallback: bool,                // True if any %fallback is seen in the grammar
	symbols_builder: SymbolsBuilder,
	prec_counter: i32,
	actions_enum: i32,
	nonterminal_types: HashMap<String, StringInFile>,
	precedence: HashMap<String, PrecedenceInFile>,
	extra_argument_type: String,
	min_shift_reduce: usize,
	error_action: usize,
	accept_action: usize,
	no_action: usize,
	min_reduce: usize,
	max_action: usize,
	no_compress: bool,                 // Don't compress the action table
	no_resort: bool,                   // Do not sort or renumber states
}
impl LemonMintBuilder
{	/// Creates new builder
	pub fn new() -> Self
	{	Self
		{	rules: Vec::with_capacity(64),
			token_type: String::new(),
			vartype: String::new(),
			start_name: String::new(),
			with_trace: false,
			trace_prompt: String::new(),
			extracode: String::new(),
			n_conflicts: 0,
			n_action_table_entries: 0,
			tables_size: 0,
			has_fallback: false,
			symbols_builder: SymbolsBuilder::new(false),
			prec_counter: 1,
			actions_enum: 0,
			nonterminal_types: HashMap::new(),
			precedence: HashMap::new(),
			extra_argument_type: String::new(),
			min_shift_reduce: 0,
			error_action: 0,
			accept_action: 0,
			no_action: 0,
			min_reduce: 0,
			max_action: 0,
			no_compress: false,
			no_resort: false,
		}
	}

	/// Find a precedence symbol of every rule in the grammar.
	///
	/// Those rules which have a precedence symbol coded in the input grammar using the `"[symbol]"` construct will already have the
	/// rule->precsym field filled.  Other rules take as their precedence symbol the first RHS symbol with a defined precedence.  If there
	/// are not RHS symbols with a defined precedence, the precedence symbol field is left blank.
	fn find_rule_precedences(rules: &mut Vec<Rule>)
	{	for rule in rules.iter_mut()
    	{	if rule.precsym.is_none()
			{	for sp in rule.rhs.iter()
				{	if sp.borrow().prec >= 0
					{	rule.precsym = Some(Rc::clone(sp));
						break;
					}
				}
			}
		}
	}

	/// Find all nonterminals which will generate the empty string.  Then go back and compute the first sets of every nonterminal.
	/// The first set is the set of all terminal symbols which can begin a string generated by that nonterminal.
	fn find_first_sets(&self, symbols: &Symbols, rules: &Vec<Rule>)
	{	for (i, symbol) in symbols.array[0 .. symbols.n_symbols].iter().enumerate()
		{	symbol.borrow_mut().lambda = false;
			if i >= symbols.n_terminals
			{	symbol.borrow_mut().firstset.set_size(symbols.n_terminals + 1);
			}
		}

		// First compute all lambdas
		let mut progress = true;
		while progress
		{	progress = false;
'l:			for rule in rules.iter()
			{	let rule = rule;
				if !rule.lhs.borrow().lambda
				{	for sp in rule.rhs.iter()
					{	assert!(sp.borrow().typ==SymbolType::NONTERMINAL || !sp.borrow().lambda);
						if !sp.borrow().lambda
						{	continue 'l;
						}
					}
					rule.lhs.borrow_mut().lambda = true;
					progress = true;
				}
			}
		}

		// Now compute all first sets
		progress = true;
		while progress
		{	progress = false;
			for rule in rules.iter()
			{	let s1 = &rule.lhs;
				for s2 in rule.rhs.iter()
				{	if s2.borrow().typ == SymbolType::TERMINAL
					{	if s1.borrow_mut().firstset.add(s2.borrow().index)
						{	progress = true;
						}
						break;
					}
					else if *s1.borrow() == *s2.borrow()
					{	if !s1.borrow().lambda
						{	break;
						}
					}
					else
					{	if s1.borrow_mut().firstset.intersect(&s2.borrow().firstset)
						{	progress = true;
						}
						if !s2.borrow().lambda
						{	break;
						}
					}
				}
			}
		}
	}

	/// Construct the propagation links
	fn find_links(states: &States)
    {	// Housekeeping detail:
		// Add to every propagate link a pointer back to the state to which the link is attached.
		for stp in states.array.iter()
		{	for cfp in stp.configurations.iter()
			{	cfp.borrow_mut().n_state = stp.n_state;
			}
		}

		// Convert all backlinks into forward links.
    	// Only the forward links are used in the follow-set computation.
    	for stp in states.array.iter()
    	{	for cfp in stp.configurations.iter()
    		{	for plp in cfp.borrow().bplp.iter()
    			{	plp.borrow_mut().fplp.insert(0, Rc::clone(&cfp)); // TODO: maybe push(), not insert()
    			}
    		}
    	}
    }

	/// Compute all followsets.
    ///
    /// A followset is the set of all symbols which can come immediately after a configuration.
    fn find_follow_sets(states: &States)
    {	for stp in states.array.iter()
    	{	for cfp in stp.configurations.iter()
    		{	cfp.borrow_mut().status_is_complete = false;
    		}
    	}

    	let mut progress = true;
		while progress
		{	progress = false;
    		for stp in states.array.iter()
    		{	for cfp in stp.configurations.iter()
    			{	if !cfp.borrow().status_is_complete
					{	for plp in cfp.borrow().fplp.iter()
						{	let mut plp = plp.borrow_mut();
							if plp.fws.intersect(&cfp.borrow().fws) // if changed
							{	plp.status_is_complete = false;
								progress = true;
							}
						}
						cfp.borrow_mut().status_is_complete = true;
					}
    			}
    		}
    	}
    }

	/// Resolve a conflict between the two given actions.  If the conflict can't be resolved, return non-zero.
    ///
    /// NO LONGER TRUE:
    ///   To resolve a conflict, first look to see if either action is on an error rule.  In that case, take the action which
    ///   is not associated with the error rule.  If neither or both actions are associated with an error rule, then try to
    ///   use precedence to resolve the conflict.
    ///
    /// If either action is a SHIFT, then it must be apx.  This function won't work if apx->type==REDUCE and apy->type==SHIFT.
    fn resolve_conflict(rules: &mut Vec<Rule>, apx: &Rc<RefCell<Action>>, apy: &Rc<RefCell<Action>>) -> usize
	{	let mut errcnt = 0;
		let mut apx = apx.borrow_mut();
		let mut apy = apy.borrow_mut();
		assert_eq!(apx.sp, apy.sp);  // Otherwise there would be no conflict
		let mut apx_typ = apx.typ;
		let mut apy_typ = apy.typ;
		if apx_typ==ActionType::Shift && apy_typ==ActionType::Shift
		{	apy_typ = ActionType::SsConflict;
			errcnt += 1;
		}
		if apx_typ==ActionType::Shift && apy_typ==ActionType::Reduce
		{	let spx = &apx.sp;
			let spx = spx.borrow();
			if let StateOrRule::Rule(n_rule) = apy.x
			{	let spy = &rules[n_rule].precsym;
				if let Some(spy) = spy
				{	let spy = spy.borrow();
					if spx.prec<0 || spy.prec<0
					{	// Not enough precedence information.
						apy_typ = ActionType::SrConflict;
						errcnt += 1;
					}
					else if spx.prec > spy.prec    // higher precedence wins
					{	apy_typ = ActionType::RdResolved;
					}
					else if spx.prec < spy.prec
					{	apx_typ = ActionType::ShResolved;
					}
					else if spx.prec==spy.prec && spx.assoc== Associativity::RIGHT // Use operator
					{	apy_typ = ActionType::RdResolved;                          // associativity
					}
					else if spx.prec==spy.prec && spx.assoc== Associativity::LEFT  // to break tie
					{	apx_typ = ActionType::ShResolved;
					}
					else
					{	assert!(spx.prec==spy.prec && spx.assoc== Associativity::NONASSOC);
						apy_typ = ActionType::Error;
					}
				}
				else
				{	// Not enough precedence information.
					apy_typ = ActionType::SrConflict;
					errcnt += 1;
				}
			}
		}
		else if apx_typ==ActionType::Reduce && apy_typ==ActionType::Reduce
		{	if let StateOrRule::Rule(n_rule_x) = apx.x
			{	if let StateOrRule::Rule(n_rule_y) = apy.x
				{	let spx = &rules[n_rule_x].precsym;
					let spy = &rules[n_rule_y].precsym;
					if let Some(spx) = spx
					{	if let Some(spy) = spy
						{	let spx = spx.borrow();
							let spy = spy.borrow();
							if spx.prec<0 || spy.prec<0 || spx.prec==spy.prec
							{	apy_typ = ActionType::RrConflict;
								errcnt += 1;
							}
							else if spx.prec > spy.prec
							{	apy_typ = ActionType::RdResolved;
							}
							else if spx.prec < spy.prec
							{	apx_typ = ActionType::RdResolved;
							}
						}
						else
						{	apy_typ = ActionType::RrConflict;
							errcnt += 1;
						}
					}
					else
					{	apy_typ = ActionType::RrConflict;
						errcnt += 1;
					}
				}
			}
		}
		else
		{	assert!
			(	apx_typ == ActionType::ShResolved ||
				apx_typ == ActionType::RdResolved ||
				apx_typ == ActionType::SsConflict ||
				apx_typ == ActionType::SrConflict ||
				apx_typ == ActionType::RrConflict ||
				apy_typ == ActionType::ShResolved ||
				apy_typ == ActionType::RdResolved ||
				apy_typ == ActionType::SsConflict ||
				apy_typ == ActionType::SrConflict ||
				apy_typ == ActionType::RrConflict
			);
			// The REDUCE/SHIFT case cannot happen because SHIFTs come before REDUCEs on the list.  If we reach this point it must be because
			// the parser conflict had already been resolved.
		}
		apx.typ = apx_typ;
		apy.typ = apy_typ;
		errcnt
    }

	/// Compute the reduce actions, and resolve conflicts.
    fn find_actions(&mut self, symbols: &Symbols, rules: &mut Vec<Rule>, states: &mut States) -> ParserResult<()>
    {	// Add all of the reduce actions
    	// A reduce action is added for each element of the followset of a configuration which has its dot at the extreme right.
    	for stp in states.array.iter_mut()   // Loop over all states
    	{	for cfp in stp.configurations.iter()  // Loop over all configurations
    		{	if cfp.borrow().dot == rules[cfp.borrow().n_rule].rhs.len()  // Is dot at extreme right?
    			{	for (j, symbol) in symbols.array.iter().take(symbols.n_terminals).enumerate()
    				{	if cfp.borrow().fws.contains(j)
    					{	// Add a reduce action to the state "stp" which will reduce by the rule "cfp->rule" if the lookahead symbol is "symbols[j]"
    						stp.actions.push(Rc::new(RefCell::new(Action::new_rule(self.actions_enum, symbol, ActionType::Reduce, cfp.borrow().n_rule))));
							self.actions_enum += 1;
    					}
    				}
    			}
    		}
    	}

    	// Add the accepting token
    	// Add to the first state (which is always the starting state of the finite state machine) an action to ACCEPT if the lookahead is the start nonterminal.
    	states.array[0].actions.push(Rc::new(RefCell::new(Action::new_empty_rule(self.actions_enum, symbols.get_start_symbol(), ActionType::Accept))));
		self.actions_enum += 1;

    	// Resolve conflicts
    	for stp in states.array.iter_mut()
    	{	if stp.actions.len() != 0
    		{	stp.actions.sort();
    			for action in stp.actions.windows(2)
				{	if action[0].borrow().sp == action[1].borrow().sp
    				{	// The two actions "action[0]" and "action[1]" have the same lookahead.
    					// Figure out which one should be used
    					self.n_conflicts += Self::resolve_conflict(rules, &action[0], &action[1]);
    				}
				}
    		}
    	}

    	// Report an error for each rule that can never be reduced.
    	for stp in states.array.iter_mut()
    	{	for action in stp.actions.iter()
    		{	if action.borrow().typ == ActionType::Reduce
				{	if let StateOrRule::Rule(n_rule) = action.borrow().x
					{	rules[n_rule].can_reduce = true;
					}
				}
    		}
    	}
    	for rule in rules.iter()
		{	if !rule.can_reduce
			{	return Err(LemonMintError::new(&rule.rule_filename, rule.rule_n_line, "This rule can not be reduced.\n".to_string()));
			}
		}
		Ok(())
    }

	fn get_filename_of_first_rule(rules: &Vec<Rule>) -> Arc<String>
	{	if let Some(rule) = rules.iter().next()
		{	return Arc::clone(&rule.rule_filename);
		}
		Arc::new("".to_string())
	}

	/// Reduce the size of the action tables, if possible, by making use of defaults.
	///
	/// In this version, we take the most frequent REDUCE action and make it the default.
	fn compress_tables(&self, symbols: &Symbols, rules: &Vec<Rule>, states: &mut States, default_symbol: &Rc<RefCell<Symbol>>)
	{	for state in states.array.iter_mut()
		{	let mut n_best = 0;
			let mut r_best = std::usize::MAX;

			let mut it = state.actions.iter();
			while let Some(action) = it.next()
			{	if action.borrow().typ == ActionType::Reduce
				{	if let StateOrRule::Rule(n_rule) = action.borrow().x
					{	let rule = &rules[n_rule];
						if !rule.lhs_start && n_rule != r_best
						{	let mut n = 1;
							let mut it2 = it.clone();
							while let Some(ap2) = it2.next()
							{	if ap2.borrow().typ == ActionType::Reduce
								{	if let StateOrRule::Rule(n_rule_2) = ap2.borrow().x
									{	if n_rule_2 != r_best && n_rule_2 == n_rule
										{	n += 1;
										}
									}
								}
							}
							if n > n_best
							{	n_best = n;
								r_best = n_rule;
							}
						}
					}
				}
			}

			// Do not make a default if the number of rules to default is not at least 1
			if n_best < 1
			{	continue;
			}

			// Combine matching REDUCE actions into a single default
			let mut found = false;
			for action in state.actions.iter()
			{	let mut action =  action.borrow_mut();
				if action.typ == ActionType::Reduce
				{	if let StateOrRule::Rule(n_rule) = action.x
					{	if rules[n_rule].index == r_best
						{	if !found
							{	action.sp = Rc::clone(default_symbol);
								found = true;
							}
							else
							{	action.typ = ActionType::NotUsed;
							}
						}
					}
				}
			}
			assert!(found);
			state.actions.sort();

			found = false;
			for action in state.actions.iter()
			{	let action = action.borrow();
				if action.typ==ActionType::Shift || action.typ==ActionType::Reduce && match action.x {StateOrRule::Rule(n_rule) => rules[n_rule].index != r_best, _ => false}
				{	found = true;
					break;
				}
			}
			if !found
			{	state.auto_reduce = true;
				state.default_reduce_rule = r_best;
			}
		}

		// Make a second pass over all states and actions.  Convert every action that is a SHIFT to an autoReduce state into a SHIFTREDUCE action.
		for stp in states.array.iter()
		{	for action in stp.actions.iter()
			{	let mut action = action.borrow_mut();
				if action.typ == ActionType::Shift
				{	if let StateOrRule::State(next_n_state) = action.x
					{	let next_state = &states.array[next_n_state];
						if next_state.auto_reduce && next_state.default_reduce_rule!=std::usize::MAX
						{	action.typ = ActionType::ShiftReduce;
							action.x = StateOrRule::Rule(next_state.default_reduce_rule);
						}
					}
				}
			}
		}

		// If a SHIFTREDUCE action specifies a rule that has a single RHS term (meaning that the SHIFTREDUCE will land back in the state where it
		// started) and if there is no C-code associated with the reduce action, then we can go ahead and convert the action to be the same as the
		// action for the RHS of the rule.
		for stp in states.array.iter()
		{	for action in stp.actions.iter()
			{	let mut done = false;
				while !done
				{	done = true;
					let mut ap2 = None;
					{	let action = action.borrow();
						if action.typ == ActionType::ShiftReduce
						{	if let StateOrRule::Rule(n_rule) = action.x
							{	let rp = &rules[n_rule];
								if rp.code.is_empty() && rp.rhs.len()==1
								{	// Only apply this optimization to non-terminals.  It would be OK to apply it to terminal symbols too, but that makes the parser tables larger.
									if action.sp.borrow().index >= symbols.n_terminals
									{	// If we reach this point, it means the optimization can be applied
										ap2 = stp.actions.iter().find
										(		|a|
											{	let a = a.borrow();
												a.id!= action.id && a.sp.borrow().index==rp.lhs.borrow().index
											}
										);
										assert!(ap2.is_some());
										done = false;
									}
								}
							}
						}
					}
					if let Some(ap2) = ap2
					{	let mut action = action.borrow_mut();
						let ap2 = ap2.borrow();
						action.sp_opt = Some(Rc::clone(&ap2.sp));
						action.typ = ap2.typ;
						action.x = ap2.x;
					}
				}
			}
		}
	}

	/// Given an action, compute the integer value for that action which is to be put in the action table of the generated machine.
	/// Return negative if no action should be generated.
	fn compute_action(&self, symbols: &Symbols, action: &Rc<RefCell<Action>>) -> usize
	{	let action = action.borrow();
		match action.typ
		{	ActionType::Shift =>
			{	match action.x
				{	StateOrRule::State(n_state) => n_state,
					_ => std::usize::MAX
				}
			}
			ActionType::ShiftReduce =>
			{	// Since a SHIFT is inherient after a prior REDUCE, convert any SHIFTREDUCE action with a nonterminal on the LHS into a simple REDUCE action:
				match action.x
				{	StateOrRule::Rule(n_rule) =>
					{	if action.sp.borrow().index >= symbols.n_terminals
						{	self.min_reduce + n_rule
						}
						else
						{	self.min_shift_reduce + n_rule
						}
					},
					_ => std::usize::MAX
				}
			}
			ActionType::Reduce =>
			{	match action.x
				{	StateOrRule::Rule(n_rule) => self.min_reduce + n_rule,
					_ => std::usize::MAX
				}
			}
			ActionType::Error =>
			{	self.error_action
			}
			ActionType::Accept =>
			{	self.accept_action
			}
			_ => std::usize::MAX
		}
	}

	/// Renumber and resort states so that states with fewer choices occur at the end.  Except, keep state 0 as the first state.
	fn resort_states(&mut self, symbols: &Symbols, states: &mut States)
	{	let sorted_len = states.array.len();
		for stp in states.array.iter_mut()
		{	stp.n_token_act = 0;
			stp.n_nt_act = 0;
			stp.default_reduce_action = std::usize::MAX; // Init dflt action to "syntax error"
			stp.token_offset = std::isize::MIN;
			stp.nt_offset = std::isize::MIN;
			for action in stp.actions.iter()
			{	let n_action = self.compute_action(symbols, action);
				if n_action != std::usize::MAX
				{	let action = action.borrow();
					if action.sp.borrow().index < symbols.n_terminals
					{	stp.n_token_act += 1;
					}
					else if action.sp.borrow().index < symbols.n_symbols
					{	stp.n_nt_act += 1;
					}
					else
					{	assert!(!stp.auto_reduce || action.x == StateOrRule::Rule(stp.default_reduce_rule));
						stp.default_reduce_action = n_action;
					}
				}
			}
		}

		// Compare two states for sorting purposes.  The smaller state is the one with the most non-terminal actions.
		// If they have the same number of non-terminal actions, then the smaller is the one with the most token actions.
		if sorted_len > 2
		{	states.array[1 ..].sort_by
			(	|a, b|
				{	let mut res = b.n_nt_act.cmp(&a.n_nt_act);
					if res == Ordering::Equal
					{	res = b.n_token_act.cmp(&a.n_token_act);
						if res == Ordering::Equal
						{	res = b.n_state.cmp(&a.n_state);
						}
					}
					res
				}
			);
		}

		// update also in actions and configurations
		let mut map = Vec::new();
		map.resize(states.array.len(), 0);
		for (i, stp) in states.array.iter().enumerate()
		{	map[stp.n_state] = i;
		}
		for stp in states.array.iter()
		{	for action in stp.actions.iter()
			{	if let StateOrRule::State(ref mut state) = action.borrow_mut().x
				{	*state = map[*state];
				}
			}
			for configuration in stp.configurations.iter()
			{	let mut configuration = configuration.borrow_mut();
				configuration.n_state = map[configuration.n_state];
			}
		}

		// update self
		for (new_n_state, stp) in states.array.iter_mut().enumerate()
		{	stp.n_state = new_n_state;
		}

		while states.n_no_tail>1 && states.array[states.n_no_tail-1].auto_reduce
		{	states.n_no_tail -= 1;
		}
	}

	/// Return the name of a C datatype able to represent values between lwr and upr, inclusive.
	fn minimum_size_type(lower: isize, upper: isize) -> isize
	{	if lower >= 0
		{	if upper <= 255
			{	1
			}
			else if upper < 65535
			{	2
			}
			else
			{	4
			}
		}
		else
		{	if lower>=-127 && upper<=127
			{	-1
			}
			else if lower>=-32767 && upper<32767
			{	-2
			}
			else
			{	-4
			}
		}
	}

	/// zCode is a string that is the action associated with a rule.  Expand the symbols in this string so that the refer to elements of the parser stack.
	fn translate_code(&self, rule: &mut Rule) -> ParserResult<()>
	{	let mut used = Vec::new();   // True for each RHS element which is used
		used.resize(rule.rhs.len(), false);

		if rule.code.is_empty()
		{	rule.line = rule.rule_n_line;
		}
		let mut it = rule.code.chars();
		let mut it_prev = it.clone();

		while let Some(cp) = it.next()
		{	if cp.is_ascii_alphabetic()
			{	let ident: String = it_prev.take_while(|c| c.is_ascii_alphanumeric() || *c=='_').collect();
				if ident.len() > 1
				{	it.nth(ident.chars().count() - 2).unwrap();
				}
				for i in 0 .. rule.rhs.len()
				{	if rule.rhs_aliases.get(i) == Some(&ident)
					{	used[i] = true;
						break;
					}
				}
			}
			it_prev = it.clone();
		}

		// Generate warnings for RHS symbols which aliases are not used in the reduce code
		for i in 0 .. rule.rhs.len()
		{	if i < rule.rhs_aliases.len()
			{	let alias: &str = &rule.rhs_aliases[i];
				if !alias.is_empty() && !used[i]
				{	return Err
					(	LemonMintError::new
						(	&rule.rule_filename,
							rule.rule_n_line,
							format!("Label {} for \"{}({})\" is never used.", alias, rule.rhs[i].borrow().name, alias)
						)
					);
				}
			}
		}

		Ok(())
	}

	/*
	** Print the definition of the union used for the parser's data stack.
	** This union contains fields for every possible data type for tokens
	** and nonterminals.  In the process of computing and printing this
	** union, also set the ".dtnum" field of every terminal and nonterminal
	** symbol.
	*/
	fn get_minor_type(&self, symbols: &Symbols) -> Vec<(String, String)>
	{	// Allocate and initialize types[] and allocate stddt[]
		let arraysize = symbols.n_symbols * 2; // Size of the "types" array
		let mut types = Vec::new(); // A hash table of datatypes
		types.resize(arraysize, String::new());

		// Build a hash table of datatypes. The ".dtnum" field of each symbol is filled in with the hash index plus 1.  A ".dtnum" value of 0 is
		// used for terminal symbols.  If there is no %default_type defined then 0 is also used as the .dtnum value for nonterminals which do not specify
		// a datatype using the %type directive.
'l:		for (i, sp) in symbols.array[0 .. symbols.n_symbols].iter().enumerate()
		{	let mut sp = &mut *sp.borrow_mut();
			if i == symbols.error_symbol_index
			{	sp.dtnum = arraysize+1;
				continue;
			}
			if sp.typ==SymbolType::TERMINAL || (sp.data_type.is_empty() && self.vartype.is_empty())
			{	sp.dtnum = 0;
				continue;
			}
			let stddt = if !sp.data_type.is_empty()
			{	&sp.data_type
			}
			else
			{	&self.vartype
			};
			if !self.token_type.is_empty() && &self.token_type == stddt
			{	sp.dtnum = 0;
				continue;
			}
			let mut hash = DefaultHasher::new();
			stddt.hash(&mut hash);
			let mut hash = hash.finish() as usize % arraysize;
			while !types[hash].is_empty()
			{	if &types[hash] == stddt
				{	sp.dtnum = hash + 1;
					continue 'l;
				}
				hash += 1;
				if hash >= arraysize
				{	hash = 0;
				}
			}
			sp.dtnum = hash + 1;
			types[hash] = stddt.to_string(); // TODO: no to_string()
		}

		// Print out the definition of TokenValue and MinorType
		let mut minor_type = Vec::with_capacity(arraysize+3);
		minor_type.push(("None".to_string(), "".to_string()));
		minor_type.push(("Symbol0".to_string(), "TokenValue".to_string()));
		let mut i = 1;
		for name in types
		{	if !name.is_empty()
			{	minor_type.push((format!("Symbol{}", i), name));
			}
			i += 1;
		}
		if let Some(symbol) = symbols.get_error_symbol()
		{	minor_type.push((format!("Symbol{}", symbol.borrow().dtnum), "i32".to_string()));
		}

		// Done
		minor_type
	}

	fn init_acttab(&mut self, symbols: &Symbols, rules: &mut Vec<Rule>, states: &mut States) -> ActTab
	{	let mut acttab = ActTab::new(symbols.n_terminals, symbols.n_symbols);

		// Compute the actions on all states and count them up
		let mut ax = Vec::with_capacity(states.n_no_tail*2);
		for stp in states.array[0 .. states.n_no_tail].iter()
		{	ax.push(AxSet::new(stp.n_state, true, stp.n_token_act, ax.len()));
			ax.push(AxSet::new(stp.n_state, false, stp.n_nt_act, ax.len()));
		}
		ax.sort();

		let mut min_token_offset = 0;
		let mut max_token_offset = 0;
		let mut min_nt_offset = 0;
		let mut max_nt_offset = 0;

		// Compute the action table.  In order to try to keep the size of the action table to a minimum, the heuristic of placing the largest action sets first is used.
		for ax_i in ax.iter()
		{	if ax_i.n_action == 0
			{	break;
			}
			let stp = &mut states.array[ax_i.n_state];
			if ax_i.is_tkn
			{	for action in stp.actions.iter()
				{	if action.borrow().sp.borrow().index < symbols.n_terminals
					{	let n_action = self.compute_action(symbols, action);
						if n_action != std::usize::MAX
						{	acttab.acttab_action(action.borrow().sp.borrow().index, n_action);
						}
					}
				}
				stp.token_offset = acttab.acttab_insert(true);
				if stp.token_offset < min_token_offset
				{	min_token_offset = stp.token_offset;
				}
				if stp.token_offset > max_token_offset
				{	max_token_offset = stp.token_offset;
				}
			}
			else
			{	for action in stp.actions.iter()
				{	if action.borrow().sp.borrow().index >= symbols.n_terminals && action.borrow().sp.borrow().index != symbols.n_symbols
					{	let n_action = self.compute_action(symbols, action);
						if n_action != std::usize::MAX
						{	acttab.acttab_action(action.borrow().sp.borrow().index, n_action);
						}
					}
				}
				stp.nt_offset = acttab.acttab_insert(false);
				if stp.nt_offset < min_nt_offset
				{	min_nt_offset = stp.nt_offset;
				}
				if stp.nt_offset > max_nt_offset
				{	max_nt_offset = stp.nt_offset;
				}
			}
		}

		// Mark rules that are actually used for reduce actions after all optimizations have been applied
		for rule in rules.iter_mut()
		{	rule.does_reduce = false;
		}
		for state in states.array[0 .. states.n_no_tail].iter()
		{	for action in state.actions.iter()
			{	let action = action.borrow_mut();
				if action.typ==ActionType::Reduce || action.typ==ActionType::ShiftReduce
				{	if let StateOrRule::Rule(n_rule) = action.x
					{	rules[n_rule].does_reduce = true;
					}
				}
			}
		}

		let mut n_fallbacks = 0;
		if self.has_fallback
		{	n_fallbacks = symbols.n_terminals - 1;
			while n_fallbacks>0 && symbols.array[n_fallbacks].borrow().fallback.is_none()
			{	n_fallbacks -= 1;
			}
			n_fallbacks += 1;
		}
		self.has_fallback = n_fallbacks != 0;

		let mut n_shift_offset = states.n_no_tail;
		while n_shift_offset >0 && states.array[n_shift_offset -1].token_offset == std::isize::MIN
		{	n_shift_offset -= 1;
		}

		let mut reduce_count = states.n_no_tail;
		while reduce_count>0 && states.array[reduce_count-1].nt_offset == std::isize::MIN
		{	reduce_count -= 1;
		}

		acttab.min_token_offset = min_token_offset;
		acttab.max_token_offset = max_token_offset;
		acttab.min_nt_offset = min_nt_offset;
		acttab.max_nt_offset = max_nt_offset;
		acttab.n_fallbacks = n_fallbacks;
		acttab.n_shift_offset = n_shift_offset;
		acttab.reduce_count = reduce_count;

		acttab
	}

	/// Generate source code for the parser
	fn get_lemon(mut self, symbols: Symbols, mut rules: Vec<Rule>, states: States, acttab: ActTab) -> ParserResult<LemonMint>
	{	// Generate types
		let sz_code_type = Self::minimum_size_type(0, symbols.n_symbols as isize+1);
		let sz_action_type =  Self::minimum_size_type(0, (states.array.len()+rules.len()+5) as isize);
		let sz_shift_offset_type =  Self::minimum_size_type(acttab.min_token_offset-1, acttab.max_token_offset);
		let sz_reduce_offset_type =  Self::minimum_size_type(acttab.min_nt_offset-1, acttab.max_nt_offset);

		// Generate token constants
		let mut token = Vec::with_capacity(symbols.n_terminals);
		for symbol in symbols.array[1 .. symbols.n_terminals].iter()
		{	token.push(Rc::clone(&symbol.borrow().name));
		}

		// Generate the table of rule information
		// Note: This code depends on the fact that rules are number sequentually beginning with 0.
		self.tables_size += rules.len() * sz_code_type.abs() as usize;

		// Generate the action table and its associates:
		//
		//  yy_action[]        A single table containing all actions.
		//  yy_lookahead[]     A table containing the lookahead for each entry in
		//                     yy_action.  Used to detect hash collisions.
		//  SHIFT_OFFSET[]    For each state, the offset into yy_action for
		//                     shifting terminals.
		//  REDUCE_OFFSET[]   For each state, the offset into yy_action for
		//                     shifting non-terminals after a reduce.
		//  DEFAULT[]       Default action for each state.

		// Output the LOOKAHEAD_AND_ACTION table
		self.n_action_table_entries = acttab.get_n_actions();
		let mut n = acttab.get_n_lookahead();
		let n_lookahead = std::cmp::max(n, symbols.n_terminals + self.n_action_table_entries);
		let mut lookahead_and_action = Vec::with_capacity(n_lookahead);
		for (i, LookaheadAction {lookahead, action}) in acttab.iter().enumerate()
		{	let lookahead = if *lookahead == std::usize::MAX {symbols.n_symbols} else {*lookahead};
			let action = if i >= self.n_action_table_entries {0} else if *action == std::usize::MAX {self.no_action} else {*action};
			lookahead_and_action.push((lookahead, action));
		}
		// Add extra entries to the end of the yy_lookahead[] table so that yy_shift_ofst[]+iToken will always be a valid index into the array,
		// even for the largest possible value of yy_shift_ofst[] and iToken.
		while n < n_lookahead
		{	lookahead_and_action.push((symbols.n_terminals, 0));
			n += 1;
		}
		self.tables_size += lookahead_and_action.len() * (sz_code_type + sz_action_type).abs() as usize;

		// Output the SHIFT_OFFSET[] table
		let mut shift_offset = Vec::with_capacity(acttab.n_shift_offset);
		for stp in states.array.iter().take(acttab.n_shift_offset)
		{	shift_offset.push(if stp.token_offset==std::isize::MIN {acttab.min_token_offset - 1} else {stp.token_offset});
		}
		self.tables_size += shift_offset.len() * sz_shift_offset_type.abs() as usize;

		// Output the REDUCE_OFFSET[] table
		let mut reduce_offset = Vec::with_capacity(acttab.reduce_count);
		for stp in states.array.iter().take(acttab.reduce_count)
		{	reduce_offset.push(if stp.nt_offset==std::isize::MIN {acttab.min_nt_offset - 1} else {stp.nt_offset});
		}
		self.tables_size += reduce_offset.len() * sz_reduce_offset_type.abs() as usize;

		// Output the default action table
		let mut default = Vec::with_capacity(states.n_no_tail);
		for stp in states.array.iter().take(states.n_no_tail)
		{	default.push(if stp.default_reduce_action!=std::usize::MAX {stp.default_reduce_action + self.min_reduce} else {self.error_action});
		}
		self.tables_size += default.len() * sz_action_type.abs() as usize;

		// Generate the table of fallback tokens
		let mut fallback = Vec::new();
		if self.has_fallback
		{	fallback.reserve(acttab.n_fallbacks);
			for symbol in symbols.array.iter().take(acttab.n_fallbacks)
			{	if let Some(ref fb) = symbol.borrow().fallback
				{	fallback.push((fb.borrow().index, Rc::clone(&symbol.borrow().name), Rc::clone(&fb.borrow().name)));
				}
				else
				{	fallback.push((0, Rc::clone(&symbol.borrow().name), Rc::new(String::new())));
				}
			}
		}
		self.tables_size += fallback.len() * sz_code_type.abs() as usize;

		// Generate a table containing the symbolic name of every symbol
		let mut token_names = Vec::new();
		if self.with_trace && symbols.n_symbols!=0
		{	token_names.reserve(symbols.n_symbols);
			for symbol in symbols.array.iter().take(symbols.n_symbols)
			{	token_names.push(Rc::clone(&symbol.borrow().name));
			}
		}

		// Generate code which execution during each REDUCE action
		for sym in symbols.array.iter()
		{	for n_rule in sym.borrow().sym_rules_arr.iter()
			{	self.translate_code(&mut rules[*n_rule])?;
			}
		}

		let start_type = symbols.get_start_symbol().borrow().data_type.clone();
		let minor_type = self.get_minor_type(&symbols);
		let n_symbols = symbols.n_symbols;
		let n_states = states.array.len();
		let n_no_tail = states.n_no_tail;
		let error_symbol = if let Some(symbol) = symbols.get_error_symbol() {symbol.borrow().index} else {0};
		let n_terminals = symbols.n_terminals;
		let n_nonterminals = symbols.n_symbols - symbols.n_terminals;

		Ok
		(	LemonMint
			{	symbols,
				rules,
				states,
				token_type: self.token_type,
				vartype: self.vartype,
				start_name: self.start_name,
				start_type,
				extra_argument_type: self.extra_argument_type,
				extracode: self.extracode,
				minor_type,
				token,

				sz_code_type,
				sz_action_type,
				sz_shift_offset_type,
				sz_reduce_offset_type,

				n_symbols,
				n_states,
				n_no_tail,
				n_fallbacks: acttab.n_fallbacks,
				error_symbol,
				with_fallback: self.has_fallback,
				shift_count: acttab.n_shift_offset-1,
				reduce_count: acttab.reduce_count-1,
				with_trace: self.with_trace,
				trace_prompt: self.trace_prompt,
				shift_min: acttab.min_token_offset,
				shift_max: acttab.max_token_offset,
				reduce_min: acttab.min_nt_offset,
				reduce_max: acttab.max_nt_offset,

				n_terminals,
				n_nonterminals,
				tables_size: self.tables_size,
				n_action_table_entries: self.n_action_table_entries,

				lookahead_and_action,
				shift_offset,
				reduce_offset,
				default,
				fallback,
				token_names,
			}
		)
	}

	/// Load a Y-grammar file. You can call this function several times to load grammar by parts, and you can call other builder methods to add/override settings.
	pub fn load_y_file(self, filename: &Arc<String>) -> ParserResult<Self>
	{	self.load_y(filename, File::open(filename.as_ref()).map_err(|e| LemonMintError::new(filename, 1, e.to_string()))?)
	}

	/// Like load_y_file(), but you give file contents as io::Read object.
	///
	/// # Example
	///
	/// ```
	/// use lemon_mint::LemonMintBuilder;
	/// use std::sync::Arc;
	///
	/// let fake_filename = Arc::new("source.y".to_string()); // will appear in error messages
	/// let builder = LemonMintBuilder::new().load_y(&fake_filename, "%token_type {f64}\nUnit ::= NEW_LINE.".as_bytes()).unwrap();
	/// ```
	pub fn load_y<R>(mut self, filename: &Arc<String>, input: R) -> ParserResult<Self> where R: io::Read
	{	let input = BufReader::new(input);
		let mut n_line = 0;
		let mut lines = input.lines();
		let mut part_till_comment: Option<String> = None; // if a multiline comment opened on a line, this line is not complete, and it will be stored here, and we will wait to closing token
'l:		while let Some(line) = lines.next()
		{	n_line += 1;
			let mut line = line.map_err(|e| LemonMintError::new(filename, n_line, e.to_string()))?;
			// comments?
			if let Some(part) = part_till_comment.take()
			{	if let Some(pos) = line.find("*/")
				{	line.replace_range(.. pos+2, &part);
				}
				else
				{	part_till_comment = Some(part);
					continue;
				}
			}
			loop
			{	if let Some(pos) = line.find('/')
				{	match line.bytes().skip(pos+1).next()
					{	Some(b'/') => // line comment
						{	line.truncate(pos);
						}
						Some(b'*') => // multiline comment
						{	if let Some(len_minus_2) = line[pos+2 ..].find("*/")
							{	line.replace_range(pos .. pos+len_minus_2+2, "");
								continue;
							}
							else
							{	line.truncate(pos);
								part_till_comment = Some(line);
								continue 'l;
							}
						}
						_ => {}
					}
				}
				break;
			}
			// comments cut from line
			let mut line = line.trim();
			if !line.is_empty()
			{	let mut directive = Directive::Rule;
				let mut symbol_name: Cow<str> = "".into();
				let mut rule_rhs: Cow<str> = "".into();
				if line.as_bytes()[0] == b'%'
				{	let pos = line.bytes().position(|c| c.is_ascii_whitespace()).unwrap_or(line.len());
					let token = &line[1 .. pos];
					line = &line[pos ..].trim_start();
					directive = match token
					{	"token_type" => Directive::TokenType,
						"type" => Directive::Type,
						"default_type" => Directive::DefaultType,
						"start_symbol" => Directive::StartSymbol,
						"trace" => Directive::Trace,
						"extra_argument" => Directive::ExtraArgument,
						"left" => Directive::Left,
						"right" => Directive::Right,
						"nonassoc" => Directive::Nonassoc,
						"fallback" => Directive::Fallback,
						"code" | "include" => Directive::Code,
						_ =>
						{	return Err(LemonMintError::new(filename, n_line, format!("Directive not supported: %{}", token)));
						}
					};
				}
				match directive
				{	Directive::Type | Directive::Fallback =>
					{	// read symbol name
						let pos = line.bytes().position(|c| !c.is_ascii_alphanumeric() && c!=b'_').unwrap_or(line.len());
						if pos == 0
						{	return Err(LemonMintError::new(filename, n_line, "Expected symbol name after %type".to_string()));
						}
						symbol_name = line[.. pos].to_string().into();
						line = &line[pos ..].trim_start();
					}
					Directive::Rule =>
					{	let pos = line.find("::=").ok_or_else(|| LemonMintError::new(filename, n_line, "Couldn't interpret this line".to_string()))?;
						symbol_name = line[.. pos].trim_end().to_string().into();
						line = &line[pos+3 ..].trim_start();
						let pos = line.find('.').ok_or_else(|| LemonMintError::new(filename, n_line, "Rules must be terminated with a dot".to_string()))?;
						rule_rhs = line[.. pos].trim_end().to_string().into();
						line = &line[pos+1 ..].trim_start();
					}
					_ => {}
				}
				let mut value: Cow<str> = line.into();
				if line.bytes().next() == Some(b'{')
				{	line = &line[1 ..].trim_start(); // skip '{' at the beginning
					let (mut balance, mut last_close) = (1, usize::MAX);
					Self::balanced_braces(filename, n_line, line, &mut balance, &mut last_close)?;
					if balance == 0
					{	value = line[.. last_close].into(); // cut '}' at the end
					}
					else
					{	// read lines untill all braces closed
						let mut buffer = String::with_capacity(128);
						buffer.push_str(line);
						buffer.push('\n');
						let from_n_line = n_line;
						while let Some(line) = lines.next()
						{	n_line += 1;
							let line = line.map_err(|e| LemonMintError::new(filename, n_line, e.to_string()))?;
							Self::balanced_braces(filename, n_line, &line, &mut balance, &mut last_close)?;
							if balance == 0
							{	buffer.push_str(&line[.. last_close]); // cut '}' at the end
								break;
							}
							buffer.push_str(&line);
							buffer.push('\n');
						}
						if balance > 0
						{	return Err(LemonMintError::new(filename, n_line, format!("Braces not closed at the end of file since line {}", from_n_line)));
						}
						value = buffer.into();
					}
				}
				else if !line.is_empty() && line.as_bytes()[line.len()-1]==b'.'
				{	value = line[.. line.len()-1].trim_end().into(); // cut '.' at end
				}
				self = match directive
				{	Directive::Rule => self.add_rule(filename, n_line, symbol_name.into(), rule_rhs.as_ref(), value.into()),
					Directive::TokenType => self.set_token_type(value.into()),
					Directive::Type => self.add_type(filename, n_line, symbol_name.into(), value.into()),
					Directive::DefaultType => self.set_default_type(value.into()),
					Directive::StartSymbol => self.set_start_symbol(filename, n_line, value.into()),
					Directive::Trace => self.set_trace_prompt(value.into()),
					Directive::ExtraArgument => self.set_extra_argument_type(value.into()),
					Directive::Left => self.set_left(filename, n_line, value.as_ref()),
					Directive::Right => self.set_right(filename, n_line, value.as_ref()),
					Directive::Nonassoc => self.set_nonassoc(filename, n_line, value.as_ref()),
					Directive::Fallback => self.add_fallback(filename, n_line, symbol_name.into(), value.as_ref()),
					Directive::Code => self.add_code(value.into()),
				}?;
			}
		}
		Ok(self)
	}

	fn balanced_braces(filename: &Arc<String>, n_line: usize, line: &str, balance: &mut i32, last_close: &mut usize) -> ParserResult<()>
	{	for (i, c) in line.bytes().enumerate()
		{	match c
			{	b'{' => *balance += 1,
				b'}' => {*balance -= 1; *last_close = i}
				_ => {}
			}
		}
		if *balance < 0
		{	return Err(LemonMintError::new(filename, n_line, "Braces on line not balanced".to_string()));
		}
		if *balance == 0
		{	if !line[*last_close+1 ..].trim_end().is_empty()
			{	return Err(LemonMintError::new(filename, n_line, "Junk after closing brace".to_string()));
			}
		}
		Ok(())
	}

	///	Set the parser "%start_symbol".
	pub fn set_start_symbol(mut self, filename: &Arc<String>, n_line: usize, mut value: String) -> ParserResult<Self>
	{	let trimmed = value.trim();
		if trimmed.len() != value.len()
		{	value = trimmed.to_string();
		}
		if value.find(|c: char| !c.is_ascii_alphanumeric() && c!='_').is_some()
		{	return Err(LemonMintError::new(filename, n_line, format!("Invalid start symbol name: {}", value)));
		}
		if is_terminal_name(&value)
		{	return Err(LemonMintError::new(filename, n_line, "Start symbol must be nonterminal".to_string()));
		}
		self.start_name = value;
		Ok(self)
	}

	///	Set the parser "%token_type".
	pub fn set_token_type(mut self, value: String) -> ParserResult<Self>
	{	self.token_type = typename_to_string(value);
		Ok(self)
	}

	///	Set the parser "%default_type".
	pub fn set_default_type(mut self, value: String) -> ParserResult<Self>
	{	self.vartype = typename_to_string(value);
		Ok(self)
	}

	///	Enable trace, and set prompt that will be printed before each message.
	pub fn set_trace_prompt(mut self, value: String) -> ParserResult<Self>
	{	self.with_trace = true;
		self.trace_prompt = value;
		Ok(self)
	}

	/// Set the parser %extra_argument.
	pub fn set_extra_argument_type(mut self, value: String) -> ParserResult<Self>
	{	self.extra_argument_type = typename_to_string(value);
		Ok(self)
	}

	///	Add the parser "%left NAME"
	pub fn set_left(self, filename: &Arc<String>, n_line: usize, symbol_names: &str) -> ParserResult<Self>
	{	self.set_associativity(filename, n_line, symbol_names, Associativity::LEFT)
	}

	///	Add the parser "%right NAME"
	pub fn set_right(self, filename: &Arc<String>, n_line: usize, symbol_names: &str) -> ParserResult<Self>
	{	self.set_associativity(filename, n_line, symbol_names, Associativity::RIGHT)
	}

	///	Add the parser "%nonassoc NAME".
	pub fn set_nonassoc(self, filename: &Arc<String>, n_line: usize, symbol_names: &str) -> ParserResult<Self>
	{	self.set_associativity(filename, n_line, symbol_names, Associativity::NONASSOC)
	}

	fn set_associativity(mut self, filename: &Arc<String>, n_line: usize, symbol_names: &str, assoc: Associativity) -> ParserResult<Self>
	{	for symbol_name in symbol_names.trim().split(|c: char| c.is_ascii_whitespace())
		{	if !symbol_name.is_empty()
			{	if symbol_name.find(|c: char| !c.is_ascii_alphanumeric() && c!='_').is_some()
				{	return Err(LemonMintError::new(filename, n_line, format!("Invalid token name: {}", symbol_name)));
				}
				if !is_terminal_name(symbol_name)
				{	return Err(LemonMintError::new(filename, n_line, format!("Can only set precedence for terminal symbols, not \"{}\"", symbol_name)));
				}
				if let Some(prev) = self.precedence.get(symbol_name)
				{	return Err(LemonMintError::new(filename, n_line, format!("Symbol \"{}\" has already be given a precedence at {}:{}", symbol_name, prev.filename, prev.n_line)));
				}
				self.precedence.insert
				(	symbol_name.to_string(),
					PrecedenceInFile
					{	filename: Arc::clone(filename),
						n_line,
						assoc,
						precedence: self.prec_counter,
					}
				);
			}
		}
		self.prec_counter += 1;
		Ok(self)
	}

	///	Add the parser "%type symbol_name {Type}".
	pub fn add_type(mut self, filename: &Arc<String>, n_line: usize, mut symbol_name: String, type_name: String) -> ParserResult<Self>
	{	let trimmed = symbol_name.trim();
		if trimmed.len() != symbol_name.len()
		{	symbol_name = trimmed.to_string();
		}
		if symbol_name.find(|c: char| !c.is_ascii_alphanumeric() && c!='_').is_some()
		{	return Err(LemonMintError::new(filename, n_line, format!("Invalid symbol name: {}", symbol_name)));
		}
		if is_terminal_name(&symbol_name)
		{	return Err(LemonMintError::new(filename, n_line, format!("Can only set type for nonterminal symbols, not \"{}\"", symbol_name)));
		}
		if let Some(prev) = self.nonterminal_types.get(&symbol_name)
		{	return Err(LemonMintError::new(filename, n_line, format!("Type for symbol \"{}\" already defined at {}:{}", symbol_name, prev.filename, prev.n_line)));
		}
		self.nonterminal_types.insert
		(	symbol_name,
			StringInFile
			{	filename: Arc::clone(filename),
				n_line,
				string: typename_to_string(type_name),
			}
		);
		Ok(self)
	}

	///	Add the parser "%fallback FB A B C".
	pub fn add_fallback(mut self, filename: &Arc<String>, n_line: usize, mut fallback_to_symbol_name: String, symbol_names: &str) -> ParserResult<Self>
	{	let trimmed = fallback_to_symbol_name.trim();
		if trimmed.len() != fallback_to_symbol_name.len()
		{	fallback_to_symbol_name = trimmed.to_string();
		}
		if fallback_to_symbol_name.find(|c: char| !c.is_ascii_alphanumeric() && c!='_').is_some()
		{	return Err(LemonMintError::new(filename, n_line, format!("Invalid token name: {}", fallback_to_symbol_name)));
		}
		let fallback_to_symbol_name = Rc::new(fallback_to_symbol_name);
		for symbol_name in symbol_names.trim().split(|c: char| c.is_ascii_whitespace())
		{	if !symbol_name.is_empty()
			{	if symbol_name.find(|c: char| !c.is_ascii_alphanumeric() && c!='_').is_some()
				{	return Err(LemonMintError::new(filename, n_line, format!("Invalid token name: {}", symbol_name)));
				}
				if !is_terminal_name(symbol_name)
				{	return Err(LemonMintError::new(filename, n_line, format!("Can only set fallback to terminal symbols, not \"{}\"", symbol_name)));
				}
				let symbol_name = Rc::new(symbol_name.to_string());
				let sp = self.symbols_builder.add(Rc::clone(&symbol_name));
				if sp.borrow().fallback.is_some()
				{	return Err(LemonMintError::new(filename, n_line, format!("More than one fallback assigned to token \"{}\"", symbol_name)));
				}
				let fsp = self.symbols_builder.add(Rc::clone(&fallback_to_symbol_name));
				if *fsp.borrow() == *sp.borrow()
				{	return Err(LemonMintError::new(filename, n_line, format!("Symbol \"{}\" is asked fallback to self // {}, {}", symbol_name, fsp.borrow().name, sp.borrow().name)));
				}
				sp.borrow_mut().fallback = Some(fsp);
			}
		}
		Ok(self)
	}

	///	Add parser rule like "a", "b(v_b) COMMA c(v_c)", "vec![v_b, v_c]"
	pub fn add_rule(mut self, filename: &Arc<String>, n_line: usize, mut lhs_name: String, rhs_names_aliases: &str, code: String) -> ParserResult<Self>
	{	let trimmed = lhs_name.trim();
		if trimmed.len() != lhs_name.len()
		{	lhs_name = trimmed.to_string();
		}
		if is_terminal_name(&lhs_name)
		{	return Err(LemonMintError::new(filename, n_line, format!("Invalid LHS symbol: \"{}\"", lhs_name)));
		}
		let mut code = code;
		if code.trim().is_empty()
		{	code = String::new();
		}
		if self.start_name.is_empty()
		{	self.start_name = lhs_name.clone();
		}
		let lhs_name = Rc::new(lhs_name);
		let mut rule = Rule::new(filename, n_line, &self.symbols_builder.add(lhs_name), self.rules.len(), code);
		// parse rhs_names_aliases
		let mut s = rhs_names_aliases.trim_start();
		while s.len() != 0
		{	let name_len = s.chars().position(|c| !c.is_ascii_alphanumeric() && c!='_').unwrap_or(s.len());
			if name_len == 0
			{	return Err(LemonMintError::new(filename, n_line, format!("Invalid RHS expression: \"{}\"", rhs_names_aliases)));
			}
			rule.rhs.push(self.symbols_builder.add(Rc::new(s[.. name_len].to_string())));
			s = s[name_len ..].trim_start();
			let mut alias = String::new();
			if s.bytes().next() == Some(b'(')
			{	s = s[1 ..].trim_start();
				let alias_len = s.chars().position(|c| !c.is_ascii_alphanumeric() && c!='_').unwrap_or(s.len());
				alias = s[.. alias_len].to_string();
				s = s[alias_len ..].trim_start();
				if alias_len==0 || s.bytes().next() != Some(b')')
				{	return Err(LemonMintError::new(filename, n_line, format!("Invalid alias in RHS expression: \"{}\"", rhs_names_aliases)));
				}
				s = s[1 ..].trim_start();
			}
			rule.rhs_aliases.push(alias);
		}
		rule.lhs.borrow_mut().sym_rules_arr.insert(0, self.rules.len()); // TODO: maybe push(), not insert()
		self.rules.push(rule);
		Ok(self)
	}

	///	Add the parser %code or %include
	pub fn add_code(mut self, code: String) -> ParserResult<Self>
	{	if self.extracode.is_empty()
		{	self.extracode = code;
		}
		else
		{	self.extracode.push_str("\n\n");
			self.extracode.push_str(&code);
		}
		Ok(self)
	}

	/// Allows to disable finite-state machine tables compression. Don't do this.
	pub fn set_no_compress(mut self, new_no_compress: bool) -> ParserResult<Self>
	{	self.no_compress = new_no_compress;
		Ok(self)
	}

	/// Disable resorting states. You don't need this functionality.
	pub fn set_no_resort(mut self, new_no_resort: bool) -> ParserResult<Self>
	{	self.no_resort = new_no_resort;
		Ok(self)
	}

	/// When you feed all the parser rules and options, call this method to finally build the parser finite-state machine transition tables.
	/// If there are problems with your grammar or if there are parser conflicts, this will return Err.
	/// If parser build succeeds this returns the parser representation as `LemonMint` object.
	pub fn try_into_lemon(mut self) -> ParserResult<LemonMint>
	{	// rules
		let mut rules = mem::replace(&mut self.rules, Vec::new());
		if rules.len() == 0
		{	return Err(LemonMintError::new(&Arc::new(String::new()), 1, "Empty grammar".to_string()));
		}
		// Put rules that have no reduce action C-code associated with them last, so that the switch() statement that selects reduction actions will have a smaller jump table.
		rules.sort_by
		(	|a, b|
			{	if a.code.is_empty() == b.code.is_empty()
				{	a.index.cmp(&b.index)
				}
				else if a.code.is_empty()
				{	Ordering::Greater
				}
				else
				{	Ordering::Less
				}
			}
		);
		for (i, rule) in rules.iter_mut().enumerate()
		{	rule.index = i;
		}

		// Count and index the symbols of the grammar
		let symbols =
		{	let symbols_builder = mem::replace(&mut self.symbols_builder, SymbolsBuilder::new(true));
			let nonterminal_types = mem::replace(&mut self.nonterminal_types, HashMap::new());
			let precedence = mem::replace(&mut self.precedence, HashMap::new());

			symbols_builder.into_symbols(&self.start_name, nonterminal_types, precedence) // symbols - Sorted array of all symbols
		}?;

		// Find the precedence for every production rule (that has one)
		Self::find_rule_precedences(&mut rules);

		// Compute the lambda-nonterminals and the first-sets for every nonterminal
		self.find_first_sets(&symbols, &rules);

		// Find the start symbol
		if !self.start_name.is_empty()
		{	if symbols.start_symbol_index == std::usize::MAX
			{	return Err(LemonMintError::new(&Self::get_filename_of_first_rule(&rules), 1, format!("The specified start symbol \"{}\" is not in a nonterminal of the grammar", self.start_name)));
			}
		}
		else
		{	return Err(LemonMintError::new(&Self::get_filename_of_first_rule(&rules), 1, "Please, specify a start symbol".to_string()));
		}

		// Make sure the start symbol doesn't occur on the right-hand side of any rule.  Report an error if it does.
		// (YACC would generate a new start symbol in this case.)
		for rule in rules.iter()
		{	for sp in rule.rhs.iter()
			{	if *sp.borrow() == *symbols.get_start_symbol().borrow()
				{	return Err(LemonMintError::new(&Self::get_filename_of_first_rule(&rules), 1, format!("The start symbol \"{}\" occurs on the right-hand side of a rule", sp.borrow().name)));
				}
			}
		}

		dump_symbols(&symbols, &rules);

		// Compute all LR(0) states.  Also record follow-set propagation links so that the follow-set can be computed later
		let mut states = StatesBuilder::build(&mut rules, symbols.get_start_symbol(), symbols.n_terminals, &mut self.actions_enum)?;

		dump_states(&states, &rules, &symbols, 1);

		// Tie up loose ends on the propagation links
		Self::find_links(&states);

		dump_states(&states, &rules, &symbols, 2);

		// Compute the follow set of every reducible configuration
		Self::find_follow_sets(&states);

		dump_states(&states, &rules, &symbols, 3);

		// Compute the action tables
		self.find_actions(&symbols, &mut rules, &mut states)?;

		dump_states(&states, &rules, &symbols, 4);

		// Compress the action tables
		if !self.no_compress
		{	self.compress_tables(&symbols, &rules, &mut states, symbols.get_default_symbol());
		}

		dump_states(&states, &rules, &symbols, 5);

		// Reorder and renumber the states so that states with fewer choices occur at the end.  This is an optimization that helps make the
		// generated parser tables smaller.
		if !self.no_resort
		{	self.resort_states(&symbols, &mut states);
		}

		dump_states(&states, &rules, &symbols, 6);

		// Compute the action table
		self.min_shift_reduce = states.array.len();
		self.error_action = self.min_shift_reduce + rules.len();
		self.accept_action = self.error_action + 1;
		self.no_action = self.accept_action + 1;
		self.min_reduce = self.no_action + 1;
		self.max_action = self.min_reduce + rules.len();
		let acttab = self.init_acttab(&symbols, &mut rules, &mut states);

		dump_states(&states, &rules, &symbols, 7);

		// Generate the source code for the parser
		if self.n_conflicts > 0
		{	Err(LemonMintError::new(&Self::get_filename_of_first_rule(&rules), 1, format!("{} parsing conflicts", self.n_conflicts)))
		}
		else
		{	self.get_lemon(symbols, rules, states, acttab)
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum Lang
{	Rust
}

fn size_type_to_str(lang: Lang, n_bytes: isize) -> &'static str
{	match (lang, n_bytes)
	{	(Lang::Rust, -1) => "i8",
		(Lang::Rust, -2) => "i16",
		(Lang::Rust, -4) => "i32",
		(Lang::Rust,  1) => "u8",
		(Lang::Rust,  2) => "u16",
		(Lang::Rust,  4) => "u32",
		(Lang::Rust,  _) => "isize",
	}
}

/// The compiled parser that can be saved to a rust file. Use `LemonMintBuilder` to build it.
#[derive(Debug)]
pub struct LemonMint
{	symbols: Symbols,
	rules: Vec<Rule>,                  // All rules
	states: States,
	token_type: String,                // Type of terminal symbols in the parser stack
	vartype: String,                   // The default type of non-terminal symbols
	start_name: String,                // Name of the start symbol for the grammar
	start_type: String,
	extra_argument_type: String,
	extracode: String,
	minor_type: Vec<(String, String)>,
	token: Vec<Rc<String>>,

	sz_code_type: isize,
	sz_action_type: isize,
	sz_shift_offset_type: isize,
	sz_reduce_offset_type: isize,

	n_symbols: usize,
	n_states: usize,
	n_no_tail: usize,
	n_fallbacks: usize,
	error_symbol: usize,
	with_fallback: bool,
	shift_count: usize,
	reduce_count: usize,
	with_trace: bool,
	trace_prompt: String,              // Prompt to preface each trace message, if with_trace is true
	shift_min: isize,
	shift_max: isize,
	reduce_min: isize,
	reduce_max: isize,

	n_terminals: usize,
	n_nonterminals: usize,
	tables_size: usize,                // Total table size of all tables in bytes
	n_action_table_entries: usize,     // Number of entries in the yy_action[] table

	lookahead_and_action: Vec<(usize, usize)>,
	shift_offset: Vec<isize>,
	reduce_offset: Vec<isize>,
	default: Vec<usize>,
	fallback: Vec<(usize, Rc<String>, Rc<String>)>,
	token_names: Vec<Rc<String>>,
}
impl LemonMint
{	/// Generate Rust source code for the parser
	pub fn gen_rust<W>(&self, out: &mut W) -> io::Result<()> where W: io::Write
	{	writeln!(out, "pub mod code {{")?;

		let mut lempar_reader = LemparReader::new();
		lempar_reader.copy_part(out)?; // to %% no. 1

		// Generate types
		writeln!(out, "pub type TokenValue = {};", if !self.token_type.is_empty() {&self.token_type} else {"String"})?;
		writeln!(out, "pub type ExtraArgumentType = {};", if !self.extra_argument_type.is_empty() {&self.extra_argument_type} else {"()"})?;
		writeln!(out, "pub type StartType = {};", if !self.start_type.is_empty() {&self.start_type} else {"()"})?;
		writeln!(out, "type CodeType = {};", size_type_to_str(Lang::Rust, self.sz_code_type))?;
		writeln!(out, "type ActionType = {};", size_type_to_str(Lang::Rust, self.sz_action_type))?;
		writeln!(out, "type ShiftOffsetType = {};", size_type_to_str(Lang::Rust, self.sz_shift_offset_type))?;
		writeln!(out, "type ReduceOffsetType = {};", size_type_to_str(Lang::Rust, self.sz_reduce_offset_type))?;

		write!(out, "enum MinorType\n{{")?;
		for (variant, typ) in self.minor_type.iter()
		{	if typ.is_empty()
			{	writeln!(out, "\t{},", variant)?;
			}
			else
			{	writeln!(out, "\t{}({}),", variant, typ)?;
			}
		}
		writeln!(out, "}}")?;

		// Generate token constants
		writeln!(out, "#[repr(u32)]\n#[allow(non_camel_case_types)]")?;
		write!(out, "pub enum Token\n{{")?;
		for (i, name) in self.token.iter().enumerate()
		{	if self.token_type.is_empty()
			{	writeln!(out, "\t{:<30} = {:2},", name, i+1)?;
			}
			else
			{	writeln!(out, "\t{:<30} = {:2},", name, i+1)?;
			}
		}
		writeln!(out, "}}\n")?;

		// Generate constants
		writeln!(out, "const NO_CODE: CodeType = {}; // YYNOCODE", self.n_symbols)?;
		writeln!(out, "const N_STATES: usize = {}; // YYNSTATE", self.n_no_tail)?;
		writeln!(out, "const N_RULES: usize = {}; // YYNRULE", self.rules.len())?;
		writeln!(out, "const N_TERMINALS: usize = {}; // YYNTOKEN", self.n_terminals)?;
		writeln!(out, "const MAX_SHIFT: usize = N_STATES-1; // YY_MAX_SHIFT")?;
		writeln!(out, "const MIN_SHIFTREDUCE: usize = {}; // YY_MIN_SHIFTREDUCE", self.n_states)?;
		writeln!(out, "const MAX_SHIFTREDUCE: usize = MIN_SHIFTREDUCE + N_RULES - 1; // YY_MAX_SHIFTREDUCE")?;
		writeln!(out, "const ERROR_ACTION: usize = MAX_SHIFTREDUCE + 1; // YY_ERROR_ACTION")?;
		writeln!(out, "const ACCEPT_ACTION: usize = ERROR_ACTION + 1; // YY_ACCEPT_ACTION")?;
		writeln!(out, "const NO_ACTION: usize = ACCEPT_ACTION + 1; // YY_NO_ACTION")?;
		writeln!(out, "const MIN_REDUCE: usize = NO_ACTION + 1; // YY_MIN_REDUCE")?;
		writeln!(out, "//const MAX_REDUCE: usize = MIN_REDUCE + N_RULES - 1; // YY_MAX_REDUCE")?;
		writeln!(out, "const ERROR_SYMBOL: CodeType = {}; // YYERRORSYMBOL", self.error_symbol)?;
		writeln!(out, "const WITH_FALLBACK: bool = {}; // YYFALLBACK", if self.n_fallbacks>0 {"true"} else {"false"})?;
		writeln!(out, "const SHIFT_COUNT: usize = {}; // YY_SHIFT_COUNT", self.shift_count)?;
		writeln!(out, "const REDUCE_COUNT: usize = {}; // YY_REDUCE_COUNT", self.reduce_count)?;
		writeln!(out, "//const SHIFT_MIN: i32 = {}; // YY_SHIFT_MIN", self.shift_min)?;
		writeln!(out, "//const SHIFT_MAX: i32 = {}; // YY_SHIFT_MAX", self.shift_max)?;
		writeln!(out, "//const REDUCE_MIN: i32 = {}; // YY_REDUCE_MIN", self.reduce_min)?;
		writeln!(out, "//const REDUCE_MAX: i32 = {}; // YY_REDUCE_MAX", self.reduce_max)?;
		writeln!(out, "const ACTTAB_COUNT: usize = {}; // YY_ACTTAB_COUNT", self.n_action_table_entries)?;
		writeln!(out, "const TRACE: bool = {};", if self.with_trace {"true"} else {"false"})?;

		// trace
		if self.trace_prompt.chars().position(|c| c=='\\' || c=='"').is_none()
		{	writeln!(out, "const TRACE_PROMPT: &str = \"{}\";", self.trace_prompt)?;
		}
		else
		{	let mut tag = String::with_capacity(self.trace_prompt.len()+1);
			for _i in 0 .. self.trace_prompt.len()+1
			{	tag.push('#');
				if !self.trace_prompt.contains(&tag)
				{	break;
				}
			}
			writeln!(out, "const TRACE_PROMPT: &str = r{tag}\"{}\"{tag};", self.trace_prompt, tag=tag)?;
		}

		// Generate the action table and its associates:
		//
		//  yy_action[]        A single table containing all actions.
		//  yy_lookahead[]     A table containing the lookahead for each entry in
		//                     yy_action.  Used to detect hash collisions.
		//  SHIFT_OFFSET[]    For each state, the offset into yy_action for
		//                     shifting terminals.
		//  REDUCE_OFFSET[]   For each state, the offset into yy_action for
		//                     shifting non-terminals after a reduce.
		//  DEFAULT[]       Default action for each state.

		// Output the LOOKAHEAD_AND_ACTION table
		write!(out, "const LOOKAHEAD_AND_ACTION: [LookaheadAndAction; {}] =", self.lookahead_and_action.len())?;
		let mut formatter = ArrayFormatter::new(2);
		for (lookahead, action) in self.lookahead_and_action.iter()
		{	formatter.separ(out)?;
			write!(out, "LookaheadAndAction {{lookahead: {:4}, action: {:4}}}", lookahead, action)?;
		}
		formatter.end(out)?;

		// Output the SHIFT_OFFSET[] table
		write!(out, "const SHIFT_OFFSET: [ShiftOffsetType; {}] =", self.shift_offset.len())?;
		let mut formatter = ArrayFormatter::new(16);
		for offset in self.shift_offset.iter()
		{	formatter.separ(out)?;
			write!(out, "{:4}", offset)?;
		}
		formatter.end(out)?;

		// Output the REDUCE_OFFSET[] table
		write!(out, "const REDUCE_OFFSET: [ReduceOffsetType; {}] =", self.reduce_offset.len())?;
		let mut formatter = ArrayFormatter::new(16);
		for offset in self.reduce_offset.iter()
		{	formatter.separ(out)?;
			write!(out, "{:4}", offset)?;
		}
		formatter.end(out)?;

		// Output the default action table
		write!(out, "const DEFAULT: [ActionType; {}] =", self.default.len())?;
		let mut formatter = ArrayFormatter::new(16);
		for action in self.default.iter()
		{	formatter.separ(out)?;
			write!(out, "{:4}", action)?;
		}
		formatter.end(out)?;

		// Next
		lempar_reader.copy_part(out)?; // to %% no. 2

		// Generate the table of fallback tokens
		write!(out, "const FALLBACK: [CodeType; {}] =", self.fallback.len())?;
		let mut formatter = ArrayFormatter::new(1);
		for (index, name, to_name) in self.fallback.iter()
		{	formatter.separ(out)?;
			write!(out, "{:3} /* {:10} => {} */", index, name, to_name)?;
		}
		formatter.end(out)?;

		// Next
		lempar_reader.copy_part(out)?; // to %% no. 3

		// Generate a table containing the symbolic name of every symbol
		write!(out, "const TOKEN_NAMES: [&str; {}] =", self.token_names.len())?;
		let mut formatter = ArrayFormatter::new(1);
		for name in self.token_names.iter()
		{	formatter.separ(out)?;
			write!(out, "{:<15}", format!("\"{}\"", name))?;
		}
		formatter.end(out)?;

		// Next
		lempar_reader.copy_part(out)?; // to %% no. 4

		// Generate a table containing a text string that describes every rule in the rule set of the grammar.
		// This information is used when tracing REDUCE actions.
		write!(out, "const RULE_NAMES: [&str; {}] =", self.rules.len())?;
		let mut formatter = ArrayFormatter::new(1);
		for rule in self.rules.iter()
		{	formatter.separ(out)?;
			write!(out, "\"{}\"", rule)?;
		}
		formatter.end(out)?;

		// Next
		lempar_reader.copy_part(out)?; // to %% no. 5

		// Generate the table of rule information
		// Note: This code depends on the fact that rules are number sequentually beginning with 0.
		write!(out, "const RULES_INFO: [CodeType; {}] =", self.rules.len())?;
		let mut formatter = ArrayFormatter::new(16);
		for rule in self.rules.iter()
		{	formatter.separ(out)?;
			write!(out, "{:4}", rule.lhs.borrow().index)?;
		}
		formatter.end(out)?;

		// Next
		lempar_reader.copy_part(out)?; // to %% no. 6

		// First output rules other than the default: rule
		for rule in self.rules.iter()
		{	if !rule.code.is_empty() // Will be default:
			{	write!(out, "\t\t\t{} =>", rule.index)?;
				let has_data_type = !rule.lhs.borrow().data_type.is_empty();
				let mut next_indent = "\t\t\t\t";
				if has_data_type && !rule.lhs_start
				{	write!(out, " MinorType::Symbol{}\n\t\t\t(\t{{", rule.lhs.borrow().dtnum)?;
					next_indent = "\t\t\t\t\t";
				}
				else
				{	write!(out, "\n\t\t\t{{")?;
				}
				let mut indent = "\t";
				let mut n_aliases = 0;
				let n_args = rule.rhs.len();
				for i in (0 .. n_args).rev()
				{	let has_alias = !rule.rhs_aliases[i].is_empty();
					if has_alias
					{	n_aliases += 1;
						writeln!(out, "{}let arg{} = self.stack.pop().unwrap();", indent, i+1)?;
					}
					else
					{	writeln!(out, "{}self.stack.pop();", indent)?;
					}
					indent = next_indent;
				}
				if n_aliases > 0
				{	write!(out, "{}{}match {}", indent, if rule.lhs_start {"let result = "} else {""}, if n_aliases>1 {"("} else {""})?;
					let mut comma = "";
					for i in 0 .. n_args
					{	if !rule.rhs_aliases[i].is_empty()
						{	write!(out, "{}arg{}.minor", comma, i+1)?;
							comma = ", ";
						}
					}
					write!(out, "{}\n{}{{\t{}", if n_aliases>1 {")"} else {""}, indent, if n_aliases>1 {"("} else {""})?;
					comma = "";
					for (i, rhs) in rule.rhs.iter().enumerate()
					{	if !rule.rhs_aliases[i].is_empty()
						{	write!(out, "{}MinorType::Symbol{}(arg{})", comma, rhs.borrow().dtnum, i+1)?;
							comma = ", ";
						}
					}
					write!(out, "{} => super::rules::do_rule_{}(&mut self.extra", if n_aliases>1 {")"} else {""}, rule.index)?;
					for i in 0 .. n_args
					{	if !rule.rhs_aliases[i].is_empty()
						{	write!(out, ", arg{}", i+1)?;
						}
					}
					if rule.lhs_start
					{	writeln!(out, "),\n{}\t_ => unreachable!()\n{}}};\n\t\t\t\tself.result = Some(result);\n\t\t\t\tMinorType::None\n\t\t\t}},", indent, indent)?;
					}
					else if has_data_type
					{	writeln!(out, "),\n{}\t_ => unreachable!()\n{}}}\n\t\t\t\t}}\n\t\t\t),", indent, indent)?;
					}
					else
					{	writeln!(out, "),\n{}\t_ => unreachable!()\n{}}};\n\t\t\t\tMinorType::None\n\t\t\t}},", indent, indent)?;
					}
				}
				else
				{	if rule.lhs_start
					{	writeln!(out, "{}self.result = Some(super::rules::do_rule_{}(&mut self.extra));\n\t\t\t\tMinorType::None\n\t\t\t}},", indent, rule.index)?;
					}
					else if has_data_type
					{	writeln!(out, "{}super::rules::do_rule_{}(&mut self.extra)\n\t\t\t}}),", indent, rule.index)?;
					}
					else
					{	writeln!(out, "{}super::rules::do_rule_{}(&mut self.extra);\n\t\t\t\tMinorType::None\n\t\t\t}},", indent, rule.index)?;
					}
				}
			}
		}
		// Finally, output the default: rule.
		writeln!(out, "\t\t\t_ =>\n\t\t\t{{\tself.stack.pop(); MinorType::None\n\t\t\t}}")?;

		// Next
		lempar_reader.copy_part(out)?; // to %% no. 7

		writeln!(out, "\n}}\n\n\nmod rules\n{{\tuse super::code::{{TokenValue, ExtraArgumentType}};")?;
		for rule in self.rules.iter()
		{	let rule = rule;
			if !rule.code.is_empty()
			{	write!(out, "\n\t/// {}\n", rule)?;
				write!(out, "\t#[inline]\n\t#[allow(non_snake_case, unused_variables)]\n")?;
				write!(out, "\tpub fn do_rule_{}(extra: &mut ExtraArgumentType", rule.index)?;
				for (i, rhs_rule) in rule.rhs.iter().enumerate()
				{	if !rule.rhs_aliases[i].is_empty()
					{	let rhs_rule = rhs_rule.borrow();
						let data_type = if rhs_rule.index < self.n_terminals
						{	"TokenValue"
						}
						else
						{	&rhs_rule.data_type
						};
						write!(out, ", {}: {}", rule.rhs_aliases[i], if data_type.is_empty() {"()"} else {data_type})?;
					}
				}
				write!(out, ")")?;
				let lhs = rule.lhs.borrow();
				if !lhs.data_type.is_empty()
				{	write!(out, " -> {}", lhs.data_type)?;
				}
				write!(out, "\n\t{{\t")?;
				let mut it = rule.code.chars();
'l:				while let Some(mut c) = it.next()
				{	'm:while c == '\n'
					{	write!(out, "\n\t\t")?;
						while let Some(c2) = it.next()
						{	if c2=='\n' || !c2.is_ascii_whitespace()
							{	c = c2;
								continue 'm;
							}
						}
						break 'l;
					}
					write!(out, "{}", c)?;
				}
				writeln!(out, "\n\t}}")?;
			}
		}
		writeln!(out, "}}\n")?;

		// End
		lempar_reader.copy_part(out)?;
		if !self.extracode.is_empty()
		{	writeln!(out, "\n\n{}", self.extracode)?;
		}

		Ok(())
	}

	/// Generate a report of the parser generated.  (the "y.output" file)
	///
	/// * `basisflag` - Print only the basis in report
	/// * `show_precedence_conflict` - Show conflicts resolved by precedence rules
	pub fn gen_log<W>(&self, out: &mut W, basisflag: bool, show_precedence_conflict: bool) -> io::Result<()> where W: io::Write
	{	for stp in self.states.array[0 .. self.states.n_no_tail].iter()
		{	writeln!(out, "State {}:", stp.n_state)?;

			for cfp in stp.configurations.iter()
			{	if basisflag
				{	let mut is_basis = false;
					for bp in stp.basis.iter()
					{	if *cfp.borrow() == *bp.borrow()
						{	is_basis = true;
							break;
						}
					}
					if !is_basis
					{	continue;
					}
				}
				if cfp.borrow().dot == self.rules[cfp.borrow().n_rule].rhs.len()
				{	let buf = format!("({})", self.rules[cfp.borrow().n_rule].index);
					write!(out, "    {:>5} ", buf)?;
				}
				else
				{	write!(out, "          ")?;
				}
				Self::config_print(&self.rules, out, cfp)?;
				writeln!(out, "")?;
			}

			writeln!(out, "")?;
			for action in stp.actions.iter()
			{	if Self::print_action(&self.rules, action, out, 30, show_precedence_conflict)?
				{	writeln!(out, "")?;
				}
			}
			writeln!(out, "")?;
		}
		writeln!(out, "----------------------------------------------------")?;
		writeln!(out, "Symbols:")?;
		for i in 0 .. self.symbols.n_symbols
		{	let sp = &self.symbols.array[i];
			write!(out, " {:>3}: {}", i, sp.borrow().name)?;
			if sp.borrow().typ == SymbolType::NONTERMINAL
			{	write!(out, ":")?;
				if sp.borrow().lambda
				{	write!(out, " <lambda>")?;
				}
				for j in 0 .. self.symbols.n_terminals
				{	if sp.borrow().firstset.len()>0 && sp.borrow().firstset.contains(j)
					{	write!(out, " {}", self.symbols.array[j].borrow().name)?;
					}
				}
			}
			writeln!(out, "")?;
		}
		Ok(())
	}

	fn config_print<W>(rules: &Vec<Rule>, out: &mut W, cfp: &Rc<RefCell<Config>>) -> io::Result<()> where W: io::Write
	{	write!(out, "{} ::=", rules[cfp.borrow().n_rule].lhs.borrow().name)?;
		for i in 0 ..= rules[cfp.borrow().n_rule].rhs.len()
		{	if i == cfp.borrow().dot
			{	write!(out, " *")?;
			}
			if i == rules[cfp.borrow().n_rule].rhs.len()
			{	break;
			}
			write!(out, " {}", rules[cfp.borrow().n_rule].rhs[i].borrow().name)?;
		}
		Ok(())
	}

	/// Print an action to the given file descriptor.  Return FALSE if nothing was actually printed.
	fn print_action<W>(rules: &Vec<Rule>, action: &Rc<RefCell<Action>>, out: &mut W, indent: usize, show_precedence_conflict: bool) -> io::Result<bool> where W: io::Write
	{	let mut result = false;
		match action.borrow().typ
		{	ActionType::Shift =>
			{	if let StateOrRule::State(n_state) = action.borrow().x
				{	write!(out, "{:>w$} shift        {:<7}", action.borrow().sp.borrow().name, n_state, w=indent)?;
					result = true;
				}
			}
			ActionType::Reduce =>
			{	if let StateOrRule::Rule(n_rule) = action.borrow().x
				{	write!(out, "{:>w$} reduce       {:<7}", action.borrow().sp.borrow().name, rules[n_rule].index, w=indent)?;
					Self::rule_print(out, &rules[n_rule], std::usize::MAX)?;
					result = true;
				}
			}
			ActionType::ShiftReduce =>
			{	if let StateOrRule::Rule(n_rule) = action.borrow().x
				{	write!(out, "{:>w$} shift-reduce {:<7}", action.borrow().sp.borrow().name, rules[n_rule].index, w=indent)?;
					Self::rule_print(out, &rules[n_rule], std::usize::MAX)?;
					result = true;
				}
			}
			ActionType::Accept =>
			{	write!(out, "{:>w$} accept", action.borrow().sp.borrow().name, w=indent)?;
				result = true;
			}
			ActionType::Error =>
			{	write!(out, "{:>w$} error", action.borrow().sp.borrow().name, w=indent)?;
				result = true;
			}
			ActionType::SrConflict | ActionType::RrConflict =>
			{	if let StateOrRule::Rule(n_rule) = action.borrow().x
				{	write!(out, "{:>w$} reduce       {:<7} ** Parsing conflict **", action.borrow().sp.borrow().name, rules[n_rule].index, w=indent)?;
					result = true;
				}
			}
			ActionType::SsConflict =>
			{	if let StateOrRule::State(n_state) = action.borrow().x
				{	write!(out, "{:>w$} shift        {:<7} ** Parsing conflict **", action.borrow().sp.borrow().name, n_state, w=indent)?;
					result = true;
				}
			}
			ActionType::ShResolved =>
			{	if show_precedence_conflict
				{	if let StateOrRule::State(n_state) = action.borrow().x
					{	write!(out, "{:>w$} shift        {:<7} -- dropped by precedence", action.borrow().sp.borrow().name, n_state, w=indent)?;
						result = true;
					}
				}
			}
			ActionType::RdResolved =>
			{	if show_precedence_conflict
				{	if let StateOrRule::Rule(n_rule) = action.borrow().x
					{	write!(out, "{:>w$} reduce {:<7} -- dropped by precedence", action.borrow().sp.borrow().name, rules[n_rule].index, w=indent)?;
						result = true;
					}
				}
			}
			ActionType::NotUsed => {}
		}
		Ok(result)
	}

	/// Print a single rule.
	fn rule_print<W>(out: &mut W, rule: &Rule, cursor: usize) -> io::Result<()> where W: io::Write
	{	write!(out, "{} ::=", rule.lhs.borrow().name)?;
		for (i, symbol) in rule.rhs.iter().enumerate()
		{	if i == cursor
			{	write!(out, " *")?;
			}
			write!(out, " {}", symbol.borrow().name)?;
		}
		if cursor == rule.rhs.len()
		{	write!(out, " *")?;
		}
		Ok(())
	}

	// Duplicate the input file without comments and without actions on rules
	pub fn gen_y<W>(&self, out: &mut W) -> io::Result<()> where W: io::Write
	{	writeln!(out, "// Symbols:")?;
		let mut maxlen = 10;
		for sp in self.symbols.array[0 .. self.symbols.n_symbols].iter()
		{	if sp.borrow().name.len() > maxlen
			{	maxlen = sp.borrow().name.len();
			}
		}
		let mut ncolumns = 76 / (maxlen+5);
		if ncolumns < 1
		{	ncolumns = 1;
		}
		let skip = (self.symbols.n_symbols+ncolumns-1) / ncolumns;
		for i in 0 .. skip
		{	write!(out, "//")?;
			for j in (i .. self.symbols.n_symbols).step_by(skip)
			{	let sp = &self.symbols.array[j];
				assert_eq!(sp.borrow().index, j);
				write!(out, " {:3} {:<w$}", maxlen, sp.borrow().name, w=maxlen)?;
			}
			writeln!(out, "")?;
		}
		writeln!(out, "")?;
		// %start_symbol
		if !self.start_name.is_empty()
		{	writeln!(out, "%start_symbol {{{}}}", self.start_name)?;
		}
		// %token_type
		if !self.token_type.is_empty()
		{	writeln!(out, "%token_type {{{}}}", self.token_type)?;
		}
		// %default_type
		if !self.vartype.is_empty()
		{	writeln!(out, "%default_type {{{}}}", self.vartype)?;
		}
		// %extra_argument
		if !self.extra_argument_type.is_empty()
		{	writeln!(out, "%extra_argument {{{}}}", self.extra_argument_type)?;
		}
		// %left, %right, %nonassoc
		let mut prec = 0;
		loop
		{	let mut has_greater_prec = false;
			let mut started = false;
			for symbol in self.symbols.array[1 .. self.symbols.n_terminals].iter()
			{	if symbol.borrow().prec >= prec
				{	if symbol.borrow().prec > prec
					{	has_greater_prec = true;
					}
					else
					{	if !started
						{	write!(out, "{}", if symbol.borrow().assoc== Associativity::LEFT {"%left"} else if symbol.borrow().assoc== Associativity::RIGHT {"%right"} else {"%nonassoc"})?;
							started = true;
						}
						write!(out, " {}", symbol.borrow().name)?;
					}
				}
			}
			if started
			{	writeln!(out, ".")?;
			}
			if !has_greater_prec
			{	break;
			}
			prec += 1;
		}
		// %type
		for symbol in self.symbols.array[self.symbols.n_terminals+1 .. self.symbols.n_symbols].iter()
		{	let symbol = symbol.borrow();
			writeln!(out, "%type {} {{{}}}", symbol.name, symbol.data_type)?;
		}
		// rules
		for rule in self.rules.iter()
		{	write!(out, "{}", rule.lhs.borrow().name)?;
			if rule.lhs.borrow().dtnum != 0
			{	write!(out, "(RESULT)")?;
			}
			write!(out, " ::=")?;
			for i in 0 .. rule.rhs.len()
			{	let sp = &rule.rhs[i];
				write!(out, " {}", sp.borrow().name)?;
				if rule.rhs_aliases.len()>i && !rule.rhs_aliases[i].is_empty()
				{	write!(out, "({})", rule.rhs_aliases[i])?;
				}
			}
			write!(out, ".")?;
			if let Some(ref precsym) = rule.precsym
			{	write!(out, " [{}]", precsym.borrow().name)?;
			}
			if !rule.code.is_empty()
			{	writeln!(out, " {{\n{}\n}}", rule.code)?;
			}
			writeln!(out, "")?;
		}
		Ok(())
	}
}
impl TryFrom<LemonMintBuilder> for LemonMint
{	type Error = LemonMintError;

	fn try_from(builder: LemonMintBuilder) -> ParserResult<Self>
	{	builder.try_into_lemon()
	}
}

#[cfg(not(feature = "with-debug"))]
fn dump_symbols(_symbols: &Symbols, _rules: &Vec<Rule>)
{
}

#[cfg(not(feature = "with-debug"))]
fn dump_states(_states: &States, _rules: &Vec<Rule>, _symbols: &Symbols, _n: i32)
{
}

#[cfg(feature = "with-debug")]
fn dump_symbols(symbols: &Symbols, rules: &Vec<Rule>)
{	use std::io::prelude::*;
	let mut out = File::create("/tmp/symbols-rust.js").unwrap();
	for s in symbols.array.iter()
	{	let s = s.borrow();
		writeln!(out, "{} ({}) {:?} #{} {:?} {} {}LAM:", s.name, s.index, s.typ, s.dtnum, s.assoc, s.prec, if s.lambda {""} else {"!"}).unwrap();
		if s.firstset.len() > 0
		{	write!(out, "  ").unwrap();
			for (j, v) in s.firstset.data.iter().enumerate()
			{	write!(out, "{}{}", if j%4==0&&j>0 {" "} else {""}, if *v {'y'} else {'n'}).unwrap();
			}
			writeln!(out).unwrap();
		}
		for n_rule in s.sym_rules_arr.iter()
		{	let rule = &rules[*n_rule];
			writeln!(out, "   {} = {}", rule.index, rule.code).unwrap();
		}
	}
	/*	The same in lemon.c:

		void dump_symbols(struct lemon *lemp)
		{	FILE *out = fopen("/tmp/symbols-c.js", "w");
			for (int i=0; i<lemp->nsymbol+1; i++)
			{	struct symbol *sym = lemp->symbols[i];
				fprintf(out, "%s (%d) %s #%d %s %d %s:\n", sym->name, sym->index, sym->type==TERMINAL?"TERMINAL":"NONTERMINAL", sym->dtnum, sym->assoc==LEFT?"LEFT":sym->assoc==RIGHT?"RIGHT":sym->assoc==NONE?"NONE":"UNKNOWN", sym->prec, sym->lambda?"LAM":"!LAM");
				if (sym->firstset)
				{	fprintf(out, "  ");
					for (int j=0; j<lemp->nterminal+1; j++)
					{	fprintf(out, "%s%c", j%4==0&&j>0 ? " " : "", sym->firstset[j]?'y':'n');
					}
					fprintf(out, "\n");
				}
				for (struct rule *rp=sym->rule; rp; rp=rp->nextlhs)
				{	const char *code = rp->code;
					if (code == nullptr) code = "";
					while (ISSPACE(code[0])) code++;
					int len = strlen(code);
					while (len>0 && ISSPACE(code[len-1])) len--;
					fprintf(out, "  %d = %.*s\n", rp->index, len, code);
				}
			}
			fclose(out);
		}
	*/
}

#[cfg(feature = "with-debug")]
fn dump_states(states: &States, rules: &Vec<Rule>, symbols: &Symbols, n: i32)
{	use std::io::prelude::*;
	let mut out = File::create(format!("/tmp/states-{}-rust.js", n)).unwrap();
	for s in states.array.iter()
	{	writeln!
		(	out,
			"{}. nTknAct={}, nNtAct={}, iTknOfst={}, iNtOfst={}, iDfltReduce={}, {} dfR{}[{}]",
			s.n_state,
			s.n_token_act,
			s.n_nt_act,
			if s.token_offset==std::isize::MIN {-1000} else {s.token_offset},
			if s.nt_offset==std::isize::MIN {-1000} else {s.nt_offset},
			if s.default_reduce_action==std::usize::MAX {-1} else {s.default_reduce_action as isize},
			if s.auto_reduce {"A"} else {"!A"},
			if s.default_reduce_rule==std::usize::MAX {-1} else {s.default_reduce_rule as isize},
			if s.default_reduce_rule==std::usize::MAX {"".to_string()} else {rules[s.default_reduce_rule].lhs.borrow().name.to_string()}
		).unwrap();
		for cfp in s.basis.iter()
		{	let cfp = cfp.borrow();
			writeln!(out, "  bs{} R{}[{}] .{}", cfp.n_state as isize, cfp.n_rule, rules[cfp.n_rule].lhs.borrow().name, cfp.dot).unwrap();
		}
		for cfp in s.configurations.iter()
		{	let cfp = cfp.borrow();
			// rule
			writeln!(out, "  cf{} R{}[{}] .{}", cfp.n_state as isize, cfp.n_rule, rules[cfp.n_rule].lhs.borrow().name, cfp.dot).unwrap();
			// fws
			let mut delim = "";
			write!(out, "{:<12}[", "").unwrap();
			for (j, v) in cfp.fws.data.iter().enumerate()
			{	if *v
				{	write!(out, "{}{}", delim, symbols.array[j].borrow().name).unwrap();
					delim = " ";
				}
			}
			writeln!(out, "]").unwrap();
			// fplp
			for cfp in cfp.fplp.iter()
			{	write!(out, "{:<12}{} (state {:2}) ", "", "To  ", cfp.borrow().n_state as isize).unwrap();
				LemonMint::config_print(rules, &mut out, cfp).unwrap();
				writeln!(out).unwrap();
			}
			// bplp
			for cfp in cfp.bplp.iter()
			{	write!(out, "{:<12}{} (state {:2}) ", "", "From", cfp.borrow().n_state as isize).unwrap();
				LemonMint::config_print(rules, &mut out, cfp).unwrap();
				writeln!(out).unwrap();
			}
		}
		for action in s.actions.iter()
		{	if LemonMint::print_action(rules, action, &mut out, 30, true).unwrap()
			{	writeln!(out).unwrap();
			}
		}
	}
	/*	The same in lemon.c:

		void dump_states(struct lemon *lemp, int n)
		{	char filename[1024];
			sprintf(filename, "/tmp/states-%d-c.js", n);
			FILE *out = fopen(filename, "w");
			showPrecedenceConflict = 1;
			for (int i=0; i<lemp->nstate; i++)
			{	struct state *stp = lemp->sorted[i];
				fprintf
				(	out,
					"%d. nTknAct=%d, nNtAct=%d, iTknOfst=%d, iNtOfst=%d, iDfltReduce=%d, %s dfR%d[%s]\n",
					stp->statenum,
					stp->nTknAct,
					stp->nNtAct,
					stp->iTknOfst==NO_OFFSET ? -1000 : stp->iTknOfst,
					stp->iNtOfst==NO_OFFSET ? -1000 : stp->iNtOfst,
					stp->iDfltReduce,
					stp->autoReduce?"A":"!A",
					stp->pDfltReduce ? stp->pDfltReduce->index : -1,
					stp->pDfltReduce ? stp->pDfltReduce->lhs->name : ""
				);
				for (struct config *cfp=stp->bp; cfp; cfp=cfp->bp)
				{	fprintf(out, "  bs%d R%d[%s] .%d\n", cfp->stp ? cfp->stp->statenum : -1, cfp->rp->index, cfp->rp->lhs->name, cfp->dot);
				}
				for (struct config *cfp=stp->cfp; cfp; cfp=cfp->next)
				{	fprintf(out, "  cf%d R%d[%s] .%d\n", cfp->stp ? cfp->stp->statenum : -1, cfp->rp->index, cfp->rp->lhs->name, cfp->dot);
					SetPrint(out, cfp->fws,lemp);
					PlinkPrint(out, cfp->fplp,"To  ");
					PlinkPrint(out, cfp->bplp,"From");
				}
				for (struct action *ap=stp->ap; ap; ap=ap->next)
				{	if (PrintAction(ap, out, 30)) fprintf(out, "\n");
				}
			}
			fclose(out);
		}
	*/
}
