use std::io;
use std::io::BufRead;

pub struct LemparReader
{	reader: io::Lines<&'static [u8]>,
}

const LEMPAR: &'static [u8] = br#"
/*
** 2000-05-29
**
** The author disclaims copyright to this source code.  In place of
** a legal notice, here is a blessing:
**
**    May you do good and not evil.
**    May you find forgiveness for yourself and forgive others.
**    May you share freely, never taking more than you give.
**
*************************************************************************
** Driver template for the LEMON parser generator.
**
** The "lemon" program processes an LALR(1) input grammar file, then uses
** this template to construct a parser.  The "lemon" program inserts text
** at each "%%" line.  Also, any "P-a-r-s-e" identifer prefix (without the
** interstitial "-" characters) contained in this template is changed into
** the value of the %name directive from the grammar.  Otherwise, the content
** of this template is copied straight through into the generate parser
** source file.
*/

/* The next sections is a series of control #defines.
** various aspects of the generated parser.
**    YYCODETYPE         is the data type used to store the integer codes
**                       that represent terminal and non-terminal symbols.
**                       "unsigned char" is used if there are fewer than
**                       256 symbols.  Larger types otherwise.
**    YYNOCODE           is a number of type YYCODETYPE that is not used for
**                       any terminal or nonterminal symbol.
**    YYFALLBACK         If defined, this indicates that one or more tokens
**                       (also known as: "terminal symbols") have fall-back
**                       values which should be used if the original symbol
**                       would not parse.  This permits keywords to sometimes
**                       be used as identifiers, for example.
**    YYACTIONTYPE       is the data type used for "action codes" - numbers
**                       that indicate what to do in response to the next
**                       token.
**    ParseTOKENTYPE     is the data type used for minor type for terminal
**                       symbols.  Background: A "minor type" is a semantic
**                       value associated with a terminal or non-terminal
**                       symbols.  For example, for an "ID" terminal symbol,
**                       the minor type might be the name of the identifier.
**                       Each non-terminal can have a different minor type.
**                       Terminal symbols all have the same minor type, though.
**                       This macros defines the minor type for terminal
**                       symbols.
**    YYMINORTYPE        is the data type used for all minor types.
**                       This is typically a union of many types, one of
**                       which is ParseTOKENTYPE.  The entry in the union
**                       for terminal symbols is called "yy0".
**    YYSTACKDEPTH       is the maximum depth of the parser's stack.  If
**                       zero the stack is dynamically sized using realloc()
**    ParseARG_SDECL     A static variable declaration for the %extra_argument
**    ParseARG_PDECL     A parameter declaration for the %extra_argument
**    ParseARG_PARAM     Code to pass %extra_argument as a subroutine parameter
**    ParseARG_STORE     Code to store %extra_argument into yypParser
**    ParseARG_FETCH     Code to extract %extra_argument from yypParser
**    ParseCTX_*         As ParseARG_ except for %extra_context
**    YYERRORSYMBOL      is the code number of the error symbol.  If not
**                       defined, then do no error processing.
**    YYNSTATE           the combined number of states.
**    YYNRULE            the number of rules in the grammar
**    YYNTOKEN           Number of terminal symbols
**    YY_MAX_SHIFT       Maximum value for shift actions
**    YY_MIN_SHIFTREDUCE Minimum value for shift-reduce actions
**    YY_MAX_SHIFTREDUCE Maximum value for shift-reduce actions
**    YY_ERROR_ACTION    The yy_action[] code for syntax error
**    YY_ACCEPT_ACTION   The yy_action[] code for accept
**    YY_NO_ACTION       The yy_action[] code for no-op
**    YY_MIN_REDUCE      Minimum value for reduce actions
**    YY_MAX_REDUCE      Maximum value for reduce actions
*/

/* The following structure represents a single element of the
** parser's stack.  Information stored includes:
**
**   +  The state number for the parser at this level of the stack.
**
**   +  The value of the token stored at this level of the stack.
**      (In other words, the "major" token.)
**
**   +  The semantic value stored at this level of the stack.  This is
**      the information used by the action routines in the grammar.
**      It is sometimes called the "minor" token.
**
** After the "shift" half of a SHIFTREDUCE action, the stateno field
** actually contains the reduce action for the second half of the
** SHIFTREDUCE.
*/
struct StackEntry
{	n_state: usize,   // The state-number
	major: CodeType,  // The major token value.  This is the code number for the token at this stack level
	minor: MinorType, // The user-supplied minor token value.  This is the value of the token
}

#[derive(Copy, Clone)]
struct LookaheadAndAction
{	lookahead: CodeType,
	action: ActionType,
}

/* Next are the tables used to determine what action to take based on the
** current state and lookahead token.  These tables are used to implement
** functions that take a state number and lookahead value and return an
** action integer.
**
** Suppose the action integer is N.  Then the action is determined as
** follows
**
**   0 <= N <= YY_MAX_SHIFT             Shift N.  That is, push the lookahead
**                                      token onto the stack and goto state N.
**
**   N between YY_MIN_SHIFTREDUCE       Shift to an arbitrary state then
**     and YY_MAX_SHIFTREDUCE           reduce by rule N-YY_MIN_SHIFTREDUCE.
**
**   N == YY_ERROR_ACTION               A syntax error has occurred.
**
**   N == YY_ACCEPT_ACTION              The parser accepts its input.
**
**   N == YY_NO_ACTION                  No such action.  Denotes unused
**                                      slots in the yy_action[] table.
**
**   N between YY_MIN_REDUCE            Reduce by rule N-YY_MIN_REDUCE
**     and YY_MAX_REDUCE
**
** The action table is constructed as a single large table named yy_action[].
** Given state S and lookahead X, the action is computed as either:
**
**    (A)   N = yy_action[ yy_shift_ofst[S] + X ]
**    (B)   N = yy_default[S]
**
** The (A) formula is preferred.  The B formula is used instead if
** yy_lookahead[yy_shift_ofst[S]+X] is not equal to X.
**
** The formulas above are for computing the action when the lookahead is
** a terminal symbol.  If the lookahead is a non-terminal (as occurs after
** a reduce action) then the yy_reduce_ofst[] array is used in place of
** the yy_shift_ofst[] array.
**
** The following are the tables generated in this section:
**
**  yy_action[]        A single table containing all actions.
**  yy_lookahead[]     A table containing the lookahead for each entry in
**                     yy_action.  Used to detect hash collisions.
**  yy_shift_ofst[]    For each state, the offset into yy_action for
**                     shifting terminals.
**  yy_reduce_ofst[]   For each state, the offset into yy_action for
**                     shifting non-terminals after a reduce.
**  yy_default[]       Default action for each state.
**
*********** Begin parsing tables **********************************************/

%%

/* The next table maps tokens (terminal symbols) into fallback tokens.
** If a construct like the following:
**
**      %fallback ID X Y Z.
**
** appears in the grammar, then ID becomes a fallback token for X, Y,
** and Z.  Whenever one of the tokens X, Y, or Z is input to the parser
** but it does not parse, the type of the token is changed to ID and
** the parse is retried before an error is thrown.
**
** This feature can be used, for example, to cause some keywords in a language
** to revert to identifiers if they keyword does not apply in the context where
** it appears.
*/

%%

/* TOKEN_NAMES:
**
** For tracing shifts, the names of all terminals and nonterminals
** are required.  The following table supplies these names */

%%

/* RULE_NAMES:
**
** For tracing reduce actions, the names of all rules are required.
*/

%%

/* RULES_INFO:
**
** The following table contains information about every rule that
** is used during the reduce.
*/

%%

/// The state of the parser is completely contained in an instance of the following structure
pub struct Parser
{	max_stack_size: usize,
	stack: Vec<StackEntry>,      // The parser's stack
	result: Option<StartType>,
	pub extra: ExtraArgumentType,
}
impl Parser
{	pub fn new(extra: ExtraArgumentType) -> Parser
	{	let mut this = Self
		{	max_stack_size: 0,
			stack: Vec::with_capacity(128),
			result: None,
			extra,
		};
		this.stack.push(StackEntry {n_state: 0, major: 0, minor: MinorType::None});
		this
	}

	/// Find the appropriate action for a parser given the terminal look-ahead token iLookAhead.
	///
	/// n_state - Current state number
	/// lookahead - The look-ahead token
	fn find_shift_action(n_state: usize, mut lookahead: CodeType) -> usize
	{	if n_state > MAX_SHIFT
		{	return n_state;
		}
		debug_assert!(n_state <= SHIFT_COUNT);
		loop
		{	let mut i = SHIFT_OFFSET[n_state] as isize;
			debug_assert!(i >= 0);
			debug_assert!(i <= ACTTAB_COUNT as isize);
			debug_assert!(i+N_TERMINALS as isize <= LOOKAHEAD_AND_ACTION.len() as isize);
			debug_assert!(lookahead != NO_CODE);
			debug_assert!((lookahead as isize) < (N_TERMINALS as isize));
			let lookahead_long = lookahead as isize;
			i += lookahead_long;
			let la = LOOKAHEAD_AND_ACTION[i as usize];
			if la.lookahead == lookahead
			{	return la.action as usize;
			}
			if WITH_FALLBACK
			{	let fallback = FALLBACK[lookahead_long as usize];
				if fallback != 0
				{	if TRACE
					{	eprintln!("{}FALLBACK {} => {}", TRACE_PROMPT, TOKEN_NAMES[lookahead_long as usize], TOKEN_NAMES[fallback as usize]);
					}
					debug_assert!(FALLBACK[fallback as usize] == 0); // Fallback loop must terminate
					lookahead = fallback;
					continue;
				}
			}
			/*if WITH_WILDCARD
			{	let la = LOOKAHEAD_AND_ACTION[i - lookahead + WILDCARD];
				if la.lookahead==WILDCARD && lookahead>0
				{	return la.action as usize;
				}
			}*/
			return DEFAULT[n_state] as usize;
		}
	}

	/// Find the appropriate action for a parser given the non-terminal look-ahead token iLookAhead.
	///
	/// n_state - Current state number
	/// lookahead - The look-ahead token
	fn find_reduce_action(n_state: usize, lookahead: CodeType) -> usize
	{	if ERROR_SYMBOL!=0 && n_state>REDUCE_COUNT
		{	return DEFAULT[n_state] as usize;
		}
		debug_assert!(n_state <= REDUCE_COUNT);
		let mut i = REDUCE_OFFSET[n_state] as isize;
		debug_assert!(lookahead != NO_CODE);
		i += lookahead as isize;
		let la = LOOKAHEAD_AND_ACTION[i as usize];
		if ERROR_SYMBOL!=0 && (la.lookahead!=lookahead || i>=ACTTAB_COUNT as isize)
		{	return DEFAULT[n_state] as usize;
		}
		debug_assert!(la.lookahead == lookahead);
		la.action as usize
	}

	/// Perform a shift action.
	///
	/// n_state - The new state to shift in
	/// major - The major token to shift in
	/// minor - Pointer to the minor token to shift in
	fn shift(&mut self, mut n_state: usize, major: CodeType, minor: MinorType)
	{	if n_state > MAX_SHIFT
		{	n_state += MIN_REDUCE - MIN_SHIFTREDUCE;
		}
		self.stack.push(StackEntry {n_state, major, minor});
		if TRACE
		{	if self.stack.len() > self.max_stack_size
			{	self.max_stack_size = self.stack.len();
			}
			if n_state < MIN_REDUCE
			{	eprintln!("{}Shift '{}', go to state {}", TRACE_PROMPT, TOKEN_NAMES[major as usize], n_state);
			}
			else
			{	eprintln!("{}Shift '{}', pending reduce {}", TRACE_PROMPT, TOKEN_NAMES[major as usize], n_state-MIN_REDUCE);
			}
		}
	}

	/// Perform a reduce action and the shift that must immediately follow the reduce.
	///
	/// The yyLookahead and yyLookaheadToken parameters provide reduce actions access to the lookahead token (if any).  The yyLookahead will be YYNOCODE
	/// if the lookahead token has already been consumed.  As this procedure is only called from one place, optimizing compilers will in-line it, which
	/// means that the extra parameters have no performance impact.
	///
	/// n_rule - Number of the rule by which to reduce
	fn reduce(&mut self, n_rule: usize) -> usize
	{	let goto_minor = match n_rule // The LHS of the rule reduced
		{	/* Beginning here are the reduction cases.  A typical example
			** follows:
			**   case 0:
			**  #line <lineno> <grammarfile>
			**     { ... }           // User supplied code
			**  #line <lineno> <thisfile>
			**     break;
			*/
%%
		};
		if TRACE
		{	if n_rule < N_RULES
			{	eprintln!("{}Reduce {} [{}], pop back to state {}.", TRACE_PROMPT, n_rule, RULE_NAMES[n_rule], self.stack.last().unwrap().n_state);
			}
		}
		let goto = RULES_INFO[n_rule]; // The next state
		let action = Self::find_reduce_action(self.stack.last().unwrap().n_state, goto); // The next action

		debug_assert!(!(action>MAX_SHIFT && action<=MAX_SHIFTREDUCE)); // There are no SHIFTREDUCE actions on nonterminals because the table generator has simplified them to pure REDUCE actions.
		debug_assert!(action != ERROR_ACTION); // It is not possible for a REDUCE to be followed by an error

		self.stack.push(StackEntry {n_state: action, major: goto, minor: goto_minor});

		if TRACE
		{	if action < MIN_REDUCE
			{	eprintln!("{}... then shift '{}', go to state {}", TRACE_PROMPT, TOKEN_NAMES[goto as usize], action);
			}
			else
			{	eprintln!("{}... then shift '{}', pending reduce {}", TRACE_PROMPT, TOKEN_NAMES[goto as usize], action-MIN_REDUCE);
			}
		}

		action
	}

	/// The main parser program.
	/// The first argument is a pointer to a structure obtained from "ParseAlloc" which describes the current state of the parser.
	/// The second argument is the major token number.  The third is the minor token.  The fourth optional argument is whatever the
	/// user wants (and specified in the grammar) and is available for use by the action routines.
	///
	/// token - The major token number.
	/// minor - The minor token number.
	pub fn add_token(&mut self, token: Token, minor: TokenValue) -> Result<(), ()>
	{	self.do_add_token(token as u32 as CodeType, MinorType::Symbol0(minor))
	}

	fn do_add_token(&mut self, major: CodeType, minor: MinorType) -> Result<(), ()>
	{	debug_assert!(self.stack.len() != 0);
		let mut error_hit = false;   // True if major has invoked an error
		let is_end_of_input = major == 0; // True if we are at the end of input

		let mut action = self.stack.last().unwrap().n_state;

		if TRACE
		{	if action < MIN_REDUCE
			{	eprintln!("{}Input '{}' in state {}", TRACE_PROMPT, TOKEN_NAMES[major as usize], action);
			}
			else
			{	eprintln!("{}Input '{}' with pending reduce {}", TRACE_PROMPT, TOKEN_NAMES[major as usize], action-MIN_REDUCE);
			}
		}

		loop
		{	debug_assert!(action == self.stack.last().unwrap().n_state);
			action = Self::find_shift_action(action, major); // The parser action
			if action <= MAX_SHIFTREDUCE
			{	debug_assert!(!is_end_of_input); // Impossible to shift the $ token
				self.shift(action, major, minor);
				break;
			}
			else if action >= MIN_REDUCE
			{	action = self.reduce(action - MIN_REDUCE);
			}
			else if action == ACCEPT_ACTION
			{	self.stack.pop();
				if TRACE
				{	eprintln!("{}Accept! Max stack size: {}", TRACE_PROMPT, self.max_stack_size);
				}
				break;
			}
			else
			{	debug_assert!(action == ERROR_ACTION);
				if TRACE
				{	eprintln!("{}Syntax Error!", TRACE_PROMPT);
				}
				if ERROR_SYMBOL != 0
				{	/* A syntax error has occurred.
					** The response to an error depends upon whether or not the grammar defines an error token "ERROR".
					**
					** This is what we do if the grammar does define ERROR:
					**
					**  * Call the %syntax_error function.
					**
					**  * Begin popping the stack until we enter a state where it is legal to shift the error symbol, then shift
					**    the error symbol.
					**
					**  * Set the error count to three.
					**
					**  * Begin accepting and shifting new tokens.  No new error processing will occur until three tokens have been
					**    shifted successfully.
					**
					*/
					if self.stack.last().unwrap().major==ERROR_SYMBOL || error_hit
					{	if TRACE
						{	eprintln!("{}Discard input token {}", TRACE_PROMPT, TOKEN_NAMES[major as usize]);
						}
						break;
					}
					error_hit = true;
					while self.stack.len() > 1
					{	action = Self::find_reduce_action(self.stack.last().unwrap().n_state, ERROR_SYMBOL);
						if action <= MAX_SHIFTREDUCE
						{	break;
						}
						if !TRACE
						{	self.stack.pop();
						}
						else
						{	let rec = self.stack.pop().unwrap();
							eprintln!("{}Popping {}", TRACE_PROMPT, TOKEN_NAMES[rec.major as usize]);
						}
					}
					if self.stack.len()>1 && !is_end_of_input
					{	self.shift(action, ERROR_SYMBOL, MinorType::None);
						continue;
					}
				}
				self.stack.truncate(1);
				return Err(());
			}
		}
		if TRACE
		{	if self.stack.len() > 1
			{	eprint!("{}Return. Stack=", TRACE_PROMPT);
				let mut delim = '[';
				for msp in self.stack[1 ..].iter()
				{	eprint!("{}{}", delim, TOKEN_NAMES[msp.major as usize]);
					delim = ' ';
				}
				eprintln!("]");
			}
		}
		Ok(())
	}

	pub fn end(&mut self) -> Result<StartType, ()>
	{	self.do_add_token(0, MinorType::None)?;
		self.stack.truncate(1);
		Ok(self.result.take().unwrap())
	}
}
"#;

impl LemparReader
{	pub fn new() -> Self
	{	Self
		{	reader: LEMPAR.lines(),
		}
	}

	pub fn copy_part<W>(&mut self, out: &mut W) -> io::Result<()> where W: io::Write
	{	while let Some(line) = self.reader.next()
		{	let line = line?;
			if &line == "%%"
			{	break;
			}
			write!(out, "{}\n", line)?;
		}
		Ok(())
	}
}
