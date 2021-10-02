use std::collections::LinkedList;

use crate::render::Render;
use crate::tokens::Token;

fn flatten(seq: LinkedList<Expression>) -> LinkedList<Expression> {
  let mut result = LinkedList::new();
  for elem in seq {
    match elem {
      Expression::Sequence(mut inner) => result.append(&mut inner),
      elem => result.push_back(elem),
    }
  }
  result
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expression {
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
  fn parse_next(seq: &mut LinkedList<Expression>) -> Option<Expression> {
    let mut result = LinkedList::new();
    while let Some(elem) = seq.pop_front() {
      match elem {
        Expression::Sequence(mut inner) => result.append(&mut inner),
        Expression::Token(token) => match token {
          Token::Raw(text) => result.push_back(Expression::Raw(text)),
          Token::Operator(text) => {
            if text == "/" {
              let numerator = if result.is_empty() {
                None
              } else {
                Some(Box::new(result.into()))
              };
              if let Some(next) = Expression::parse_next(seq) {
                return Some(Expression::Fraction {
                  numerator,
                  denominator: Some(Box::new(next)),
                });
              } else {
                return Some(Expression::Fraction {
                  numerator,
                  denominator: None,
                });
              }
            } else {
              result.push_back(Expression::Symbol(text))
            }
          }
          Token::Symbol(text) | Token::Delimiter(text) => {
            result.push_back(Expression::Symbol(text))
          }
          Token::Text(text) => result.push_back(Expression::Text { text, font: None }),
          Token::Font(font) => {
            let next = seq.pop_front();
            if let Some(Expression::Token(Token::Text(text))) = next {
              result.push_back(Expression::Text {
                text,
                font: Some(font),
              });
            } else if let Some(next) = next {
              seq.push_front(next)
            }
          }
          Token::LeftBracket(_) => todo!(),
          Token::RightBracket(_) => todo!(),
          Token::BracketFunction(_) => todo!(),
          Token::Function(_, _) => todo!(),
          Token::Subsup(_) => todo!(),
          Token::Whitespace => break,
        },
        elem => result.push_back(elem),
      }
    }
    match result.len() {
      0 => None,
      1 => result.pop_front(),
      _ => Some(Expression::Sequence(result)),
    }
  }

  fn parse_sequence(mut seq: LinkedList<Expression>) -> Expression {
    let mut result = LinkedList::new();
    while !seq.is_empty() {
      if let Some(elem) = Expression::parse_next(&mut seq) {
        let back = result.pop_back();
        if let Some(Expression::Fraction {
          denominator: None,
          numerator,
        }) = back
        {
          let frac = Expression::Fraction {
            numerator,
            denominator: Some(Box::new(elem)),
          };
          result.push_back(frac);
          continue;
        } else if let Some(back) = back {
          result.push_back(back);
        }
        match elem {
          Expression::Fraction {
            numerator,
            denominator,
          } => {
            if numerator.is_none() {
              let frac = Expression::Fraction {
                numerator: if let Some(back) = result.pop_back() {
                  if let Expression::Sequence(inner) = back {
                    Some(Box::new(inner.into()))
                  } else {
                    Some(Box::new(back))
                  }
                } else {
                  None
                },
                denominator,
              };
              result.push_back(frac);
            } else {
              result.push_back(Expression::Fraction {
                numerator,
                denominator,
              })
            }
          }
          elem => result.push_back(elem),
        }
      }
    }
    if result.len() == 1 {
      result.pop_back().unwrap()
    } else {
      Expression::Sequence(flatten(result))
    }
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
    assert_eq!(parse(tokenize(" / 2bx")), frac(None, Some(raw("2bx"))));
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
