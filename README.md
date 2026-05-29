# lemon-mint

A pure-Rust port of the famous [Lemon parser generator](https://www.hwaci.com/sw/lemon/), packaged
as a **library with an API** instead of a command-line tool.

You describe an LALR(1) grammar — either as a Lemon-style `.y` grammar string/file, or by calling
builder methods — and lemon-mint emits a self-contained Rust source file containing the parser's
state-machine tables and a small driver. The generated parser is plain Rust with **no runtime
dependency on this crate**, so you can commit it to your repository or generate it from a `build.rs`
build script.

Unlike a hand-written recursive-descent parser, the output is a table-driven bottom-up
(shift/reduce) LALR(1) parser: compact, fast, and able to report grammar conflicts at generation
time rather than surprising you at run time.

## The three steps

1. Build a grammar with `LemonMintBuilder`. Either feed it a whole grammar with `load_y()` /
   `load_y_file()`, or assemble it piece by piece with `set_start_symbol()`, `set_token_type()`,
   `add_type()`, `add_rule()`, and friends. The two styles can be mixed freely.
2. Compile the grammar into the parser tables with `try_into_lemon()`, which returns a `LemonMint`.
   Grammar errors and unresolved parser conflicts are reported here as an `Err`.
3. Emit Rust source with `gen_rust()`. Optionally write a human-readable report of the state machine
   with `gen_log()` (the classic Lemon `y.output`), or a normalized copy of the grammar with
   `gen_y()`.

## Example: a calculator

This generates a parser for newline-separated arithmetic expressions, then runs it on `15 / 5` to
get `3.0`:

```rust
use std::sync::Arc;
use lemon_mint::LemonMintBuilder;

let builder = LemonMintBuilder::new().load_y
(	&Arc::new("source.y".to_string()), // fake source name, that will appear in error messages
	"	%trace {>> }
		%extra_argument {()}
		%left PLUS MINUS.
		%left TIMES DIVIDE.
		%token_type {f64}
		%type Expr {super::Expr}
		%type Exprs {Vec<super::Expr>}
		%type Program {Vec<super::Expr>}

		Program ::= Exprs(exprs). exprs
		Program ::= Exprs(exprs) NEW_LINE. exprs

		Exprs ::= Expr(item).                       vec![item]
		Exprs ::= Exprs(items) NEW_LINE Expr(item). let mut items = items; items.push(item); items

		Expr ::= NUM(value). super::Expr {value}
		Expr ::= PAR_OPEN Expr(a) PAR_CLOSE. a
		Expr ::= PLUS Expr(a). a
		Expr ::= MINUS Expr(a). let mut a = a; a.value = -a.value; a
		Expr ::= Expr(a) PLUS Expr(b). super::Expr{value: a.value + b.value}
		Expr ::= Expr(a) MINUS Expr(b). super::Expr{value: a.value - b.value}
		Expr ::= Expr(a) TIMES Expr(b). super::Expr{value: a.value * b.value}
		Expr ::= Expr(a) DIVIDE Expr(b). super::Expr{value: a.value / b.value}

		%code {
			use code::{Parser, Token};

			#[derive(Debug, PartialEq)]
			pub struct Expr {value: f64}

			fn main()
			{	let mut parser = Parser::new(()); // () is our extra argument, accessible in actions and through parser.extra

				parser.add_token(Token::NUM, 15.0).unwrap();
				parser.add_token(Token::DIVIDE, 0.0).unwrap();
				parser.add_token(Token::NUM, 5.0).unwrap();
				parser.add_token(Token::NEW_LINE, 0.0).unwrap();

				let result = parser.end().unwrap(); // type is %type of the start symbol Program
				assert_eq!(result, vec![Expr {value: 3.0}]);
				println!("Result: {:?}", result);
			}
		}
	".as_bytes()
).unwrap();

let lemon = builder.try_into_lemon().unwrap();

// Emit the parser. Here we write to in-memory buffers; in practice you would write `parser.rs`
// (e.g. to `OUT_DIR` from a build script) and `include!` it.
let mut out_rust: Vec<u8> = Vec::new();
let mut out_log: Vec<u8> = Vec::new();
lemon.gen_rust(&mut out_rust).unwrap();
lemon.gen_log(&mut out_log, false, false).unwrap();
```

## Using the generated parser

`gen_rust()` wraps everything in a `code` module. The two items you use from it are `Token` (an enum
with one variant per terminal symbol) and `Parser`:

```rust
use code::{Parser, Token};

let mut parser = Parser::new(extra);           // `extra` is the initial %extra_argument value
parser.add_token(Token::NUM, 15.0)?;           // feed terminals in input order, with their values
parser.add_token(Token::DIVIDE, 0.0)?;
parser.add_token(Token::NUM, 5.0)?;
let result = parser.end()?;                    // finish; result has the start symbol's %type
```

`add_token` returns `Err(())` on a syntax error, and `end` returns `Err(())` if the input is not a
complete sentence of the grammar. The whole driver lives in `code`; a second `rules` module holds the
action code and is not used directly. Items from your crate are reachable from actions and `%code` as
`super::…` or `crate::…` (e.g. `super::Expr`).

### Soft keywords with `try_add_token`

`Parser::try_add_token` is a non-committal variant of `add_token`: it returns `Ok(true)` if the token
is accepted in the current state, or `Ok(false)` if it is not — **without** raising a syntax error.
This lets a tokenizer treat a word as a keyword where the grammar expects one and fall back to feeding
it as an identifier elsewhere ("soft" / non-reserved keywords):

```rust
match parser.try_add_token(Token::DAY, value) {
    Ok(true)  => {}                                      // consumed as the DAY keyword
    Ok(false) => parser.add_token(Token::IDENT, ident)?, // not valid here — re-feed as identifier
    Err(())   => return Err(SyntaxError),
}
```

## Y-grammar reference

lemon-mint accepts a grammar syntax close to [classic Lemon](https://www.hwaci.com/sw/lemon/). Line
(`//`) and block (`/* … */`) C-style comments are allowed anywhere.

### Rules and actions

A rule is `Lhs ::= Rhs.` optionally followed by an action — Rust code producing the semantic value of
the left-hand side:

```
Expr ::= Expr(a) PLUS Expr(b). super::Expr{value: a.value + b.value}
```

The `.` ends the right-hand side; everything after it (up to the next rule or directive) is the
action. A rule with no action produces `()`. Parenthesized names like `(a)` are **aliases** that bind
the semantic value of that symbol to a variable usable in the action. The action also has `&mut extra`
in scope (the `%extra_argument`).

### Terminals vs nonterminals

A symbol whose name contains at least one lowercase letter is a **nonterminal**; an all-uppercase name
is a **terminal** (a `Token`). (Classic Lemon decides this from the first letter only.)

### Types

Every symbol carries a semantic value. Terminals all share the `%token_type`. Each nonterminal's type
is set with `%type Name {Type}`, or defaults to `%default_type`. The start symbol's type is what the
generated `Parser::end` returns.

### Precedence and associativity

`%left`, `%right`, and `%nonassoc` declare terminal precedence to resolve shift/reduce conflicts. Each
successive declaration binds more tightly than the previous one:

```
%left PLUS MINUS.    // lower precedence
%left TIMES DIVIDE.  // higher precedence
```

### Supported directives

| Directive | Purpose |
|---|---|
| `%token_type {T}` | Type of every terminal's semantic value |
| `%type Name {T}` | Type of one nonterminal's semantic value |
| `%default_type {T}` | Default type for nonterminals without a `%type` |
| `%start_symbol Name` | The grammar's start symbol |
| `%extra_argument {T}` | Type of the user value threaded through the parser (name is always `extra`, default `()`) |
| `%left` / `%right` / `%nonassoc` | Terminal precedence and associativity |
| `%fallback FB A B C.` | Tokens `A B C` fall back to `FB` when they have no action in the current state |
| `%trace {prompt}` | Enable tracing to stderr, prefixing each message with `prompt` |
| `%code` / `%include` | Verbatim Rust code appended to the generated file (synonyms) |

Directive syntax is permissive — braces, a trailing `.`, or a bare token all work, and a braced value
may span multiple lines up to its matching closing brace:

```
%start_symbol {Unit}
%start_symbol Unit.
%start_symbol Unit
```

## Differences from classic Lemon

* A symbol is a nonterminal if its name contains any lowercase letter (classic Lemon looks only at the
  first letter).
* Tracing is enabled by the `%trace` directive rather than a `ParseTrace()` call.
* No `%name` directive — each generated file is its own Rust module.
* No destructors — Rust's ownership and `Drop` handle cleanup.

## License

MIT. The bundled Lemon driver template carries the original public-domain blessing from SQLite's
Lemon.
