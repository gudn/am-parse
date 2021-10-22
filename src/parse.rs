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
  if let Some(Expression::Token(Token::Whitespace)) = seq.front() {
    seq.pop_front();
  }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct FunctionExtra {
  pub sup: Option<Box<Expression>>,
  pub sub: Option<Box<Expression>>,
  pub derivative_level: u32,
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
    extra: FunctionExtra,
    args: Vec<Option<Expression>>,
  },
  Bracketed {
    left: String,
    right: Option<String>,
    inner: Box<Expression>,
  },
  Matrix {
    left: String,
    right: Option<String>,
    items: Vec<Vec<Expression>>,
  },
}

impl From<LinkedList<Expression>> for Expression {
  fn from(mut value: LinkedList<Expression>) -> Expression {
    if value.len() == 1 {
      value.pop_front().unwrap()
    } else {
      Expression::Sequence(value)
    }
  }
}

impl Expression {
  fn parse_function_extra(seq: &mut LinkedList<Expression>) -> FunctionExtra {
    let mut extra = FunctionExtra::default();
    while let Some(expr) = seq.front() {
      match expr {
        Expression::Token(Token::Symbol(ref op)) if extra.sup.is_none() && op == "'" => {
          extra.derivative_level += 1;
          seq.pop_front();
        }
        Expression::Token(Token::Subsup(ref op)) if extra.sub.is_none() && op == "_" => {
          extra.sub = Expression::parse_one(seq).map(Box::new);
        }
        Expression::Token(Token::Symbol(ref op)) if extra.sup.is_none() && op == "'" => {
          extra.derivative_level += 1;
          seq.pop_front();
        }
        Expression::Token(Token::Subsup(ref op))
          if extra.sup.is_none() && extra.derivative_level == 0 && op == "^" =>
        {
          extra.sup = Expression::parse_one(seq).map(Box::new);
        }
        _ => break,
      };
    }
    extra
  }

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
          Token::LeftBracket(left) => {
            let mut level = 1;
            let mut items: Vec<Vec<Expression>> = vec![vec![]];
            let mut current = Vec::new();
            let mut right = None;
            while !seq.is_empty() && level > 0 {
              let item = seq.pop_front().unwrap();
              match item {
                Expression::Token(token) => match token {
                  Token::LeftBracket(l) => {
                    level += 1;
                    current.push(Expression::Token(Token::LeftBracket(l)));
                  }
                  Token::RightBracket(r) => {
                    level -= 1;
                    if level == 0 {
                      right = Some(r);
                    } else {
                      current.push(Expression::Token(Token::RightBracket(r)));
                    }
                  }
                  Token::Delimiter(delim) => {
                    if level == 1 && delim == ";" {
                      if !current.is_empty() {
                        items
                          .last_mut()
                          .unwrap()
                          .push(Expression::Sequence(current.drain(..).collect()));
                      }
                      if !items.last().map_or(true, Vec::is_empty) {
                        items.push(vec![]);
                      }
                    } else if level == 1 && delim == "," {
                      if !current.is_empty() {
                        items
                          .last_mut()
                          .unwrap()
                          .push(Expression::Sequence(current.drain(..).collect()));
                      } else {
                        items.last_mut().unwrap().push(Expression::None);
                      }
                    } else {
                      current.push(Expression::Token(Token::Delimiter(delim)))
                    }
                  }
                  _ => current.push(Expression::Token(token)),
                },
                _ => current.push(item),
              }
            }
            if !current.is_empty() {
              items
                .last_mut()
                .unwrap()
                .push(Expression::Sequence(current.into_iter().collect()));
            } else if items.last().map_or(false, Vec::is_empty) {
              items.pop();
            }
            Expression::parse_brackets(left, right, items)
          }
          Token::RightBracket(_) => Expression::parse_one(seq),
          Token::BracketFunction(func) => {
            let extra = Expression::parse_function_extra(seq);
            let arg = if let Some(Expression::Token(Token::Whitespace)) = seq.front() {
              skip_whitespace(seq);
              Expression::parse_next(seq)
            } else {
              Expression::parse_one(seq)
            };
            if let Some(Expression::Bracketed { .. } | Expression::Matrix { .. }) = arg {
              Some(Expression::Function {
                func,
                extra,
                args: vec![arg],
              })
            } else if let Some(Expression::Sequence(inner)) = arg {
              let mut args = inner;
              while let Some(Expression::Symbol(ref symbol)) = args.back() {
                if symbol == "," {
                  skip_whitespace(seq);
                  match Expression::parse_next(seq) {
                    Some(Expression::Sequence(mut inner)) => args.append(&mut inner),
                    Some(expr) => args.push_back(expr),
                    None => break,
                  }
                } else {
                  break;
                }
              }
              Some(Expression::Function {
                func,
                extra,
                args: vec![Some(Expression::Bracketed {
                  left: "(".into(),
                  right: Some(")".into()),
                  inner: Box::new(flatten(args).into()),
                })],
              })
            } else if let Some(expr) = arg {
              Some(Expression::Function {
                func,
                extra,
                args: vec![Some(Expression::Bracketed {
                  left: "(".into(),
                  right: Some(")".into()),
                  inner: Box::new(expr),
                })],
              })
            } else {
              Some(Expression::Function {
                func,
                extra,
                args: vec![Some(Expression::Bracketed {
                  left: "(".into(),
                  right: Some(")".into()),
                  inner: Box::new(Expression::None),
                })],
              })
            }
          }
          Token::Function(func, argc) => {
            let extra = Expression::parse_function_extra(seq);
            let args: Vec<Option<Expression>> = (0..argc)
              .map(|_| {
                if let Some(Expression::Token(Token::Whitespace)) = seq.front() {
                  skip_whitespace(seq);
                  Expression::parse_next(seq)
                } else {
                  Expression::parse_one(seq)
                }
              })
              .collect();
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
            if let Some(Expression::Fraction {
              numerator: None,
              denominator,
            }) = front
            {
              let back = result.pop_back().or(Some(Expression::None));
              inner.push_front(Expression::Fraction {
                denominator,
                numerator: back.map(Box::new),
              })
            } else if let Some(Expression::Sub { base: None, sub }) = front {
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

  fn parse_brackets(
    left: String,
    right: Option<String>,
    mut items: Vec<Vec<Expression>>,
  ) -> Option<Expression> {
    match items.len() {
      0 => Some(Expression::Bracketed {
        left,
        right,
        inner: Box::new(Expression::None),
      }),
      1 => match items[0].len() {
        0 => Some(Expression::Bracketed {
          left,
          right,
          inner: Box::new(Expression::None),
        }),
        _ => {
          let mut inner = LinkedList::new();
          for elem in items[0].drain(..) {
            match elem.parse() {
              Expression::Sequence(mut seq) => inner.append(&mut seq),
              elem => inner.push_back(elem),
            }
            inner.push_back(Expression::Symbol(",".into()));
          }
          inner.pop_back();
          Some(Expression::Bracketed {
            left,
            right,
            inner: Box::new(Expression::from(inner).parse()),
          })
        }
      },
      _ => {
        let inner = items
          .into_iter()
          .map(|row| row.into_iter().map(Expression::parse).collect())
          .collect();
        Some(Expression::Matrix {
          left,
          right,
          items: inner,
        })
      }
    }
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

  fn symbol(value: &str) -> Expression {
    Expression::Symbol(value.into())
  }

  fn text(text: &str, font: Option<&str>) -> Expression {
    Expression::Text {
      text: text.into(),
      font: font.map(String::from),
    }
  }

  fn seq(values: Vec<Expression>) -> Expression {
    let seq: LinkedList<_> = values.into_iter().collect();
    Expression::Sequence(seq)
  }

  fn sup(base: Option<&str>, sup: Option<&str>) -> Expression {
    Expression::Sup {
      base: base.map(pt).map(Box::new),
      sup: sup.map(pt).map(Box::new),
    }
  }

  fn sub(base: Option<&str>, sub: Option<&str>) -> Expression {
    Expression::Sub {
      base: base.map(pt).map(Box::new),
      sub: sub.map(pt).map(Box::new),
    }
  }

  fn pt(input: &str) -> Expression {
    parse(tokenize(input, vec![]))
  }

  fn frac(numerator: &str, denominator: &str) -> Expression {
    Expression::Fraction {
      numerator: Some(numerator).map(pt).map(Box::new),
      denominator: Some(denominator).map(pt).map(Box::new),
    }
  }

  fn func(f: &str, args: Vec<&str>, extra: &str) -> Expression {
    let mut extra: LinkedList<_> = tokenize(extra, vec![])
      .into_iter()
      .map(Expression::Token)
      .collect();
    Expression::Function {
      func: f.into(),
      args: args
        .into_iter()
        .map(|s| if s.is_empty() { None } else { Some(pt(s)) })
        .collect(),
      extra: Expression::parse_function_extra(&mut extra),
    }
  }

  fn bracketed(left: &str, inner: &str, right: &str) -> Expression {
    Expression::Bracketed {
      left: left.into(),
      right: if right.is_empty() {
        None
      } else {
        Some(right.into())
      },
      inner: Box::new(pt(inner)),
    }
  }

  fn matrix(left: &str, items: Vec<Vec<&str>>, right: &str) -> Expression {
    Expression::Matrix {
      left: left.into(),
      right: if right.is_empty() {
        None
      } else {
        Some(right.into())
      },
      items: items
        .into_iter()
        .map(|row| row.into_iter().map(pt).collect())
        .collect(),
    }
  }

  #[test]
  fn parse_one_plus_one() {
    let mut seq = LinkedList::new();
    seq.push_back(raw("1"));
    seq.push_back(symbol("+"));
    seq.push_back(raw("1"));
    let result = Expression::Sequence(seq);
    assert_eq!(pt("1 + 1"), result);
    assert_eq!(pt("1+ 1"), result);
    assert_eq!(pt("1+1"), result);
  }

  #[test]
  fn parse_fracs() {
    assert_eq!(pt("1/ 2bx"), frac("1", "2bx"));
    assert_eq!(pt("1/2bx"), frac("1", "2bx"));
    assert_eq!(pt("1 /2bx"), frac("1", "2bx"));
    assert_eq!(pt("1 / 2"), frac("1", "2"));
    assert_eq!(pt("1 / 2bx"), frac("1", "2bx"));
    assert_eq!(
      pt(" / 2bx"),
      Expression::Fraction {
        numerator: Some(Box::new(Expression::None)),
        denominator: Some(Box::new(pt("2bx")))
      }
    );
    assert_eq!(
      pt("1 + 1/2+1"),
      seq(vec![raw("1"), symbol("+"), frac("1", "2+1")])
    );
    assert_eq!(
      pt("1 + 1/2 +1"),
      seq(vec![
        raw("1"),
        symbol("+"),
        frac("1", "2"),
        symbol("+"),
        raw("1"),
      ])
    );
  }

  #[test]
  fn parse_text() {
    assert_eq!(pt(r#" "hello""#), text("hello", None));
    assert_eq!(pt(r#"bb"hello""#), text("hello", Some("bb")));
    assert_eq!(pt(r#"bb "hello""#), text("hello", None),);
  }

  #[test]
  fn parse_subsup() {
    assert_eq!(pt("1^2"), sup(Some("1"), Some("2")));
    assert_eq!(pt("1_2"), sub(Some("1"), Some("2")));
    assert_eq!(pt("1_2^3"), sup(Some("1_2"), Some("3")));
    assert_eq!(pt("1^2_3"), sub(Some("1^2"), Some("3")));
    assert_eq!(pt("1^ 2+3"), sup(Some("1"), Some("2+3")));
    assert_eq!(
      pt("1^2+3"),
      seq(vec![sup(Some("1"), Some("2")), symbol("+"), raw("3")])
    );
    assert_eq!(pt("1/2^3"), frac("1", "2^3"));
  }

  #[test]
  fn parse_function() {
    assert_eq!(pt("sinx"), func("sin", vec!["x"], ""));
    assert_eq!(pt("sin x+y"), func("sin", vec!["x+y"], ""));
    assert_eq!(pt("root3 x^2"), func("root", vec!["3", "x^2"], ""));
    assert_eq!(pt("sin x^2"), func("sin", vec!["x^2"], ""));
    assert_eq!(pt("1+2 /sinx^2"), frac("1+2", "sinx^2"));
    assert_eq!(pt("sin'x"), func("sin", vec!["x"], "'"));
    assert_eq!(pt("gcd"), func("gcd", vec!["", ""], ""));
    assert_eq!(
      pt("cos^2_2x"),
      Expression::Function {
        func: "cos".into(),
        args: vec![Some(raw("x"))],
        extra: FunctionExtra {
          sup: Some(Box::new(sup(None, Some("2")))),
          sub: Some(Box::new(sub(None, Some("2")))),
          ..Default::default()
        }
      }
    );
    assert_eq!(
      pt("cos 2x = cos^2x - sin^2x"),
      seq(vec![
        func("cos", vec!["2x"], ""),
        symbol("="),
        func("cos", vec!["x"], "^2"),
        symbol("-"),
        func("sin", vec!["x"], "^2"),
      ])
    );
    assert_eq!(
      pt("lcm'_2' 12 20"),
      Expression::Function {
        func: "lcm".into(),
        args: vec![Some(raw("12")), Some(raw("20"))],
        extra: FunctionExtra {
          derivative_level: 2,
          sub: Some(Box::new(sub(None, Some("2")))),
          ..Default::default()
        }
      }
    );
    assert_eq!(
      pt("lcm_2 12 20 = 4"),
      seq(vec![
        func("lcm", vec!["12", "20"], "_2"),
        symbol("="),
        raw("4")
      ])
    );
    assert_eq!(
      pt("1/ln(3x) ="),
      seq(vec![frac("1", "ln(3x)"), symbol("="),])
    );
  }

  #[test]
  fn parse_bracketed() {
    assert_eq!(pt("(a + b)"), bracketed("(", "a+b", ")"));
    assert_eq!(pt("(1/2"), bracketed("(", "1/2", ""));
    assert_eq!(pt("[1, 2, 3]"), bracketed("[", "1, 2, 3", "]"));
    assert_eq!(pt("sin (2x + 1"), func("sin", vec!["(2x + 1"], ""));
    assert_eq!(pt("(1;2)"), matrix("(", vec![vec!["1"], vec!["2"]], ")"));
    assert_eq!(pt("1^(2+1)"), sup(Some("1"), Some("(2 + 1)")));
    assert_eq!(
      pt("(1;(2;3,4"),
      Expression::Matrix {
        left: "(".into(),
        right: None,
        items: vec![
          vec![raw("1")],
          vec![Expression::Matrix {
            left: "(".into(),
            right: None,
            items: vec![vec![raw("2")], vec![raw("3"), raw("4")]]
          }]
        ]
      }
    );
  }

  #[test]
  fn parse_bracketed_function() {
    assert_eq!(pt("max a, b"), func("max", vec!["(a, b)"], ""));
    assert_eq!(pt("min (a, b"), func("min", vec!["(a, b"], ""));
    assert_eq!(
      pt("min {1;2:} = 1"),
      seq(vec![func("min", vec!["{1;2:}"], ""), symbol("="), raw("1")])
    );
  }

  #[test]
  fn parse_complex_expression() {
    assert_eq!(
      pt("sum_ i=1 ^n i^3 = (n(n+1) /2) ^2"),
      seq(vec![
        sup(Some("sum_ i=1"), Some("n"),),
        sup(Some("i"), Some("3")),
        symbol("="),
        sup(Some("(n(n+1) /2)"), Some("2"))
      ])
    );
    assert_eq!(pt("sum_ i=1"), sub(Some("sum"), Some("i=1")));
    assert_eq!(pt("n(n+1) /2"), frac("n(n+1)", "2"));
  }

  #[test]
  fn parse_simple_expression() {
    assert_eq!(
      parse(tokenize(
        "f(x) = sinx ; f'(x) = cosx ; f''(x) = -sinx",
        vec!["f"]
      )),
      seq(vec![
        func("f", vec!["(x)"], ""),
        symbol("="),
        func("sin", vec!["x"], ""),
        symbol(";"),
        func("f", vec!["(x)"], "'"),
        symbol("="),
        func("cos", vec!["x"], ""),
        symbol(";"),
        func("f", vec!["(x)"], "''"),
        symbol("="),
        symbol("-"),
        func("sin", vec!["x"], ""),
      ])
    );
  }

  #[test]
  fn parse_fractions_with_supsub() {
    assert_eq!(
      pt("1+2 /(x+1)^6 ="),
      seq(vec![frac("1+2", "(x+1)^6"), symbol("="),])
    );
  }
}
