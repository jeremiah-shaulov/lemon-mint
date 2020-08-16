# lemon-mint
Famous Lemon Parser Generator implemented in rust as library with API.

## Example

```rust
extern crate lemon_mint;

use std::fs::File;
use std::sync::Arc;
use lemon_mint::LemonMintBuilder;

fn main()
{	let builder = LemonMintBuilder::new().load_y
	(	&Arc::new("source.y".to_string()), // fake source name, that will appear in error messages
		"	%trace {>> }
			%extra_argument {()}
			%left PLUS MINUS.
			%left DIVIDE TIMES.
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
				{	let mut parser = Parser::new(()); // () is our extra argument, that will be accessible in actions, and also through parser.extra

					parser.add_token(Token::NUM, 15.0).unwrap();
					parser.add_token(Token::DIVIDE, 0.0).unwrap();
					parser.add_token(Token::NUM, 5.0).unwrap();
					parser.add_token(Token::NEW_LINE, 0.0).unwrap();

					let result = parser.end().unwrap(); // if Program
                    assert_eq!(result, vec![Expr {value: 3.0}]);
                    println!(\"Result: {:?}\", result);
				}
			}
		".as_bytes()
	).unwrap();

	let lemon = builder.try_into_lemon().unwrap();
	let mut out_rust = File::create("/tmp/lem/ca/src/main.rs").unwrap();
	let mut out_y = File::create("/tmp/main.y").unwrap();
	lemon.gen_rust(&mut out_rust).unwrap();
	lemon.gen_log(&mut out_y, false, false).unwrap();
}
```

The first step is to create `LemonMintBuilder` object, and use it's methods to describe the desired parser. It's possible to load "y"-grammar from a file with `load_y_file()`, or from a string with `load_y()`, as shown in the example above, or you can set each parser rule with individual methods, like `set_start_symbol()`, `set_token_type()`, `add_type()`, `add_rule()`, and others.

Then the builder object can be converted to `LemonMint` object that represents the parser transition tables. This step is done with the `try_into_lemon()` method, as shown above.

And the last step is to generate a rust file with parser tables and it's driver code. This is done with `gen_rust()` method. Optionally you can generate log file with `gen_log()`, as classic Lemon program does.

## Y-Grammar

Lemon-mint uses y-grammar similar to what [classic Lemon parser](https://www.hwaci.com/sw/lemon/) uses. There are a few distinctions:

* If a symbol name contains at least one lowercase letter, it's considered nonterminal. In classic Lemon only the first letter matters.
* To enable trace, use `%trace` directive. In Lemon need to call ParseTrace() function.
* No need for `%name` directive, because in rust each file is separate module.
* No need for destructors.

The generated parser will be separated to 2 submodules: `code` and `rules`. There are only 2 interesting things in `code` module: `Parser` and `Token`. See in above example how they're used. The `rules` module wraps actions, and you don't need to use it directly. If your actions use types, constants or functions global space, they can be accessed like `super::Expr`, or `crate::Expr`, or so.

The following directives are supported:

* %token_type
* %type
* %default_type
* %start_symbol
* %trace
* %extra_argument - only it's type. The name is always `extra`. Default type is `()`.
* %left
* %right
* %nonassoc
* %fallback
* %code or %include - are the same

The syntax is free and permissive:

```
%start_symbol {Unit}
/* or */
%start_symbol Unit.
/* or */
%start_symbol Unit
```

Braces allow to specify multiline value, till matching closing brace.
