use std::collections::LinkedList;

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
  Sub {
    base: Option<Box<Expression>>,
    sub: Option<Box<Expression>>,
  },
  Sup {
    base: Option<Box<Expression>>,
    sup: Option<Box<Expression>>,
  },
  Function {
    func: String,
    extra: Vec<Expression>,
    args: Vec<Option<Expression>>,
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
          Token::Function(func, argc) => {
            let mut extra = Vec::new();
            loop {
              match seq.front() {
                Some(&Expression::Token(ref token)) => match token {
                  Token::Symbol(op) if op == "'" => {
                    let next = Expression::parse_one(seq);
                    if let Some(next) = next {
                      extra.push(next);
                    } else {
                      break;
                    }
                  }
                  Token::Subsup(_) => {
                    let next = Expression::parse_one(seq);
                    if let Some(next) = next {
                      extra.push(next);
                    } else {
                      break;
                    }
                  }
                  _ => break,
                },
                _ => break,
              };
            }
            skip_whitespace(seq);
            let args: Vec<Option<Expression>> =
              (0..argc).map(|_| Expression::parse_next(seq)).collect();
            Some(Expression::Function { func, args, extra })
          }
          Token::Subsup(op) => {
            let next = if let Some(Expression::Token(Token::Whitespace)) = seq.front() {
              skip_whitespace(seq);
              Expression::parse_next(seq).map(Box::new)
            } else {
              Expression::parse_one(seq).map(Box::new)
            };
            if op == "_" {
              Some(Expression::Sub {
                base: None,
                sub: next,
              })
            } else {
              Some(Expression::Sup {
                base: None,
                sup: next,
              })
            }
          }
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
        Expression::Sub { base: None, sub } => {
          let back = result.pop_back();
          result.push_back(Expression::Sub {
            base: back.map(Box::new),
            sub,
          })
        }
        Expression::Sup { base: None, sup } => {
          let back = result.pop_back();
          result.push_back(Expression::Sup {
            base: back.map(Box::new),
            sup,
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
          Expression::Sub { base: None, sub } => {
            let back = result.pop_back().or(Some(Expression::None));
            result.push_back(Expression::Sub {
              base: back.map(Box::new),
              sub,
            })
          }
          Expression::Sup { base: None, sup } => {
            let back = result.pop_back().or(Some(Expression::None));
            result.push_back(Expression::Sup {
              base: back.map(Box::new),
              sup,
            })
          }
          Expression::Sequence(mut inner) => {
            let front = inner.pop_front();
            if let Some(Expression::Sub { base: None, sub }) = front {
              let back = result.pop_back().or(Some(Expression::None));
              inner.push_front(Expression::Sub {
                base: back.map(Box::new),
                sub,
              });
            } else if let Some(Expression::Sup { base: None, sup }) = front {
              let back = result.pop_back().or(Some(Expression::None));
              inner.push_front(Expression::Sup {
                base: back.map(Box::new),
                sup,
              });
            } else if let Some(front) = front {
              inner.push_front(front);
            }
            result.push_back(inner.into())
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

  fn sraw(value: &str) -> Option<Expression> {
    Some(raw(value))
  }

  fn seqraw(value: Vec<&str>) -> Expression {
    seq(value.into_iter().map(raw).collect())
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

  fn sub(base: Option<Expression>, sub: Option<Expression>) -> Expression {
    Expression::Sub {
      base: base.map(Box::new),
      sub: sub.map(Box::new),
    }
  }

  fn sup(base: Option<Expression>, sup: Option<Expression>) -> Expression {
    Expression::Sup {
      base: base.map(Box::new),
      sup: sup.map(Box::new),
    }
  }

  fn func(text: &str, args: Vec<Option<Expression>>) -> Expression {
    Expression::Function {
      func: text.into(),
      extra: vec![],
      args,
    }
  }

  fn funce(text: &str, args: Vec<Option<Expression>>, extra: Vec<Expression>) -> Expression {
    Expression::Function {
      func: text.into(),
      extra,
      args,
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

  fn ptok(input: &str) -> Expression {
    parse(tokenize(input))
  }

  #[test]
  fn parse_one_plus_one() {
    assert_eq!(
      ptok("1 + 1"),
      seq(vec![raw("1"), symbol("+"), raw("1")])
    );
    assert_eq!(
      ptok("1+ 1"),
      seq(vec![raw("1"), symbol("+"), raw("1")])
    );
    assert_eq!(
      ptok("1+1"),
      seq(vec![raw("1"), symbol("+"), raw("1")])
    );
  }

  #[test]
  fn parse_fracs() {
    assert_eq!(
      ptok("1/ 2bx"),
      frac(sraw("1"), Some(seqraw(vec!["2", "b", "x"])))
    );
    assert_eq!(
      ptok("1/2bx"),
      frac(sraw("1"), Some(seqraw(vec!["2", "b", "x"])))
    );
    assert_eq!(
      ptok("1 /2bx"),
      frac(sraw("1"), Some(seqraw(vec!["2", "b", "x"])))
    );
    assert_eq!(
      ptok("1 / 2bx"),
      frac(sraw("1"), Some(seqraw(vec!["2", "b", "x"])))
    );
    assert_eq!(
      ptok(" / 2bx"),
      frac(Some(Expression::None), Some(seqraw(vec!["2", "b", "x"])))
    );
    assert_eq!(
      ptok("1 + 1/2+1"),
      seq(vec![
        raw("1"),
        symbol("+"),
        frac(sraw("1"), Some(seq(vec![raw("2"), symbol("+"), raw("1")])))
      ])
    )
  }

  #[test]
  fn parse_text() {
    assert_eq!(ptok(r#" "hello""#), text("hello", None));
    assert_eq!(ptok(r#"bb"hello""#), text("hello", Some("bb")));
    assert_eq!(ptok(r#"bb "hello""#), text("hello", None),);
  }

  #[test]
  fn parse_subsup() {
    assert_eq!(ptok("1^2"), sup(sraw("1"), sraw("2")));
    assert_eq!(ptok("1_2"), sub(sraw("1"), sraw("2")));
    assert_eq!(
      ptok("1_2^3"),
      sup(Some(sub(sraw("1"), sraw("2"))), sraw("3"))
    );
    assert_eq!(
      ptok("1^2_3"),
      sub(Some(sup(sraw("1"), sraw("2"))), sraw("3"))
    );
    assert_eq!(
      ptok("1^ 2+3"),
      sup(sraw("1"), Some(seq(vec![raw("2"), symbol("+"), raw("3")])))
    );
    assert_eq!(
      ptok("1^2+3"),
      seq(vec![sup(sraw("1"), sraw("2")), symbol("+"), raw("3")])
    );
    assert_eq!(
      ptok("1/2^3"),
      frac(sraw("1"), Some(sup(sraw("2"), sraw("3"))))
    );
  }

  #[test]
  fn parse_function() {
    assert_eq!(ptok("sinx"), func("sin", vec![sraw("x")]));
    assert_eq!(
      ptok("sin x+y"),
      func(
        "sin",
        vec![Some(seq(vec![raw("x"), symbol("+"), raw("y")]))]
      )
    );
    assert_eq!(
      ptok("root3 x^2"),
      func(
        "root",
        vec![Some(raw("3")), Some(sup(sraw("x"), sraw("2")))]
      )
    );
    assert_eq!(
      ptok("1+2 /sinx^2"),
      frac(
        Some(seq(vec![raw("1"), symbol("+"), raw("2")])),
        Some(func("sin", vec![Some(sup(sraw("x"), sraw("2")))]))
      )
    );
    assert_eq!(
      ptok("sin'x = cosx"),
      seq(vec![
        funce("sin", vec![sraw("x")], vec![symbol("'")]),
        symbol("="),
        func("cos", vec![sraw("x")])
      ])
    );
    assert_eq!(
      ptok("cos2x = cos^2x - sin^2x"),
      seq(vec![
        func("cos", vec![Some(seqraw(vec!["2", "x"]))]),
        symbol("="),
        funce("cos", vec![sraw("x")], vec![sup(None, sraw("2"))]),
        symbol("-"),
        funce("sin", vec![sraw("x")], vec![sup(None, sraw("2"))]),
      ]),
    );
    assert_eq!(
      ptok("sin^2'x = sin 2x"),
      seq(vec![
        funce(
          "sin",
          vec![sraw("x")],
          vec![sup(None, sraw("2")), symbol("'")]
        ),
        symbol("="),
        func("sin", vec![Some(seqraw(vec!["2", "x"]))])
      ])
    );
    assert_eq!(
      ptok("lcm_2 12 20 = 4"),
      seq(vec![
        funce(
          "lcm",
          vec![sraw("12"), sraw("20")],
          vec![sub(None, sraw("2"))]
        ),
        symbol("="),
        raw("4")
      ])
    );
    assert_eq!(ptok("gcd"), func("gcd", vec![None, None]));
  }
}
