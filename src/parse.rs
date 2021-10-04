use std::collections::LinkedList;

use crate::render::Render;
use crate::tokens::Token;

fn flatten(seq: LinkedList<Expression>) -> LinkedList<Expression> {
  let mut result = LinkedList::new();
  for elem in seq {
    match elem {
      Expression::Sequence(inner) => result.append(&mut flatten(inner)),
      elem => result.push_back(elem),
    }
  }
  result
}

fn skip_whitespace(seq: &mut LinkedList<Expression>) {
  while let Some(Expression::Token(Token::Whitespace)) = seq.front() {
    seq.pop_front();
  }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expression {
  None,
  Sequence(LinkedList<Expression>),
  Token(Token),
  Raw(String),
  Symbol(String),
  Fraction {
    numerator: Option<Box<Expression>>,
    denominator: Option<Box<Expression>>,
  },
  Text {
    text: String,
    font: Option<String>,
  },
  Subsup {
    base: Option<Box<Expression>>,
    sup: Option<Box<Expression>>,
    sub: Option<Box<Expression>>,
  },
}

impl From<LinkedList<Expression>> for Expression {
  fn from(mut value: LinkedList<Expression>) -> Expression {
    match value.len() {
      1 => value.pop_front().unwrap(),
      _ => Expression::Sequence(value),
    }
  }
}

impl Expression {
  /// Should return only one next item: function, subsup, fraction, bracket,
  /// text. On Whitespace token return None
  fn parse_one(seq: &mut LinkedList<Expression>) -> Option<Expression> {
    if let Some(next) = seq.pop_front() {
      match next {
        Expression::Token(token) => match token {
          Token::Raw(raw) => Some(Expression::Raw(raw)),
          Token::Symbol(symbol) => Some(Expression::Symbol(symbol)),
          Token::Delimiter(delimiter) => Some(Expression::Symbol(delimiter)),
          Token::Text(text) => Some(Expression::Text { text, font: None }),
          Token::Font(font) => {
            let next = seq.pop_front();
            if let Some(Expression::Token(Token::Text(text))) = next {
              Some(Expression::Text {
                text,
                font: Some(font),
              })
            } else if let Some(next) = next {
              seq.push_front(next);
              None
            } else {
              None
            }
          }
          Token::Operator(op) => {
            if op == "/" {
              skip_whitespace(seq);
              Some(Expression::Fraction {
                numerator: None,
                denominator: Expression::parse_next(seq).map(Box::new),
              })
            } else {
              Some(Expression::Symbol(op))
            }
          }
          Token::LeftBracket(_) => todo!(),
          Token::RightBracket(_) => todo!(),
          Token::BracketFunction(_) => todo!(),
          Token::Function(_, _) => todo!(),
          Token::Subsup(_) => todo!(),
          Token::Whitespace => None,
        },
        expr => Some(expr),
      }
    } else {
      None
    }
  }

  /// Should parse one hunk (between spaces)
  fn parse_next(seq: &mut LinkedList<Expression>) -> Option<Expression> {
    let mut result = LinkedList::new();
    while let Some(expr) = Expression::parse_one(seq) {
      match expr {
        Expression::Fraction {
          numerator: None,
          denominator,
        } => {
          let back = result.pop_back();
          result.push_back(Expression::Fraction {
            denominator,
            numerator: back.map(Box::new),
          })
        }
        expr => result.push_back(expr),
      }
    }
    if result.is_empty() {
      None
    } else {
      Some(result.into())
    }
  }

  fn parse_sequence(mut seq: LinkedList<Expression>) -> Expression {
    let mut result = LinkedList::new();
    while !seq.is_empty() {
      if let Some(expr) = Expression::parse_next(&mut seq) {
        match expr {
          Expression::Fraction {
            numerator: None,
            denominator,
          } => {
            let back = result.pop_back().or(Some(Expression::None));
            result.push_back(Expression::Fraction {
              denominator,
              numerator: back.map(Box::new),
            })
          }
          expr => result.push_back(expr),
        }
      }
    }
    flatten(result).into()
  }

  fn parse(self) -> Expression {
    match self {
      Expression::Sequence(seq) => Expression::parse_sequence(seq),
      elem => elem,
    }
  }
}

impl Render for Expression {
  fn render(&self, _: crate::OutputFormat) -> String {
    unimplemented!()
  }
}

pub fn parse(tokens: Vec<Token>) -> Expression {
  let expr = Expression::Sequence(tokens.into_iter().map(Expression::Token).collect());
  expr.parse()
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::tokens::tokenize;

  fn raw(value: &str) -> Expression {
    Expression::Raw(value.into())
  }

  fn symbol(value: &str) -> Expression {
    Expression::Symbol(value.into())
  }

  fn frac(numerator: Option<Expression>, denominator: Option<Expression>) -> Expression {
    Expression::Fraction {
      numerator: numerator.map(Box::new),
      denominator: denominator.map(Box::new),
    }
  }

  fn text(text: &str, font: Option<&str>) -> Expression {
    Expression::Text {
      text: text.into(),
      font: font.map(String::from),
    }
  }

  fn seq(value: Vec<Expression>) -> Expression {
    Expression::Sequence(value.into_iter().collect())
  }

  #[test]
  fn parse_one_plus_one() {
    assert_eq!(
      parse(tokenize("1 + 1")),
      seq(vec![raw("1"), symbol("+"), raw("1")])
    );
    assert_eq!(
      parse(tokenize("1+ 1")),
      seq(vec![raw("1"), symbol("+"), raw("1")])
    );
    assert_eq!(
      parse(tokenize("1+1")),
      seq(vec![raw("1"), symbol("+"), raw("1")])
    );
  }

  #[test]
  fn parse_fracs() {
    assert_eq!(
      parse(tokenize("1/ 2bx")),
      frac(Some(raw("1")), Some(raw("2bx")))
    );
    assert_eq!(
      parse(tokenize("1/2bx")),
      frac(Some(raw("1")), Some(raw("2bx")))
    );
    assert_eq!(
      parse(tokenize("1 /2bx")),
      frac(Some(raw("1")), Some(raw("2bx")))
    );
    assert_eq!(
      parse(tokenize("1 / 2bx")),
      frac(Some(raw("1")), Some(raw("2bx")))
    );
    assert_eq!(parse(tokenize(" / 2bx")), frac(Some(Expression::None), Some(raw("2bx"))));
    assert_eq!(
      parse(tokenize("1 + 1/2+1")),
      seq(vec![
        raw("1"),
        symbol("+"),
        frac(
          Some(raw("1")),
          Some(seq(vec![raw("2"), symbol("+"), raw("1")]))
        )
      ])
    )
  }

  #[test]
  fn parse_text() {
    assert_eq!(parse(tokenize(r#" "hello""#)), text("hello", None));
    assert_eq!(parse(tokenize(r#"bb"hello""#)), text("hello", Some("bb")));
    assert_eq!(parse(tokenize(r#"bb "hello""#)), text("hello", None),);
  }
}
