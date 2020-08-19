use std::sync::Arc;
use lemon_mint::LemonMintBuilder;

#[test]
fn test_1()
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
	let mut tmp = Vec::new();
	lemon.gen_rust(&mut tmp).unwrap();
	let mut tmp = Vec::new();
	lemon.gen_log(&mut tmp, false, false).unwrap();
}
