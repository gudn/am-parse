use crate::parse::Expression;
use crate::trie::Trie;

trait Renderer {
  fn render(&mut self, expr: Expression);

  fn result(&self) -> String;
}

enum LatexState {
  NeedSpace,
  NeedWrap,
}

struct LatexRenderer {
  result: String,
  symbols: Trie<String>,
  state: Option<LatexState>,
}

impl LatexRenderer {
  fn new() -> LatexRenderer {
    let mut symbols = Trie::new();
    let lines = std::include_str!("latex_symbols.toml");
    for line in lines.lines() {
      let mut line = line.split(" := ");
      let key = line.next();
      let value = line.next();
      if key.is_some() && value.is_some() {
        symbols.insert(key.unwrap(), value.unwrap().to_owned())
      }
    }
    LatexRenderer {
      result: String::new(),
      symbols,
      state: None,
    }
  }

  fn set_state(&mut self, state: LatexState) {
    self.state = Some(state);
  }

  fn clear_state(&mut self) {
    self.state = None;
  }
}

impl Renderer for LatexRenderer {
  fn render(&mut self, expr: Expression) {
    match expr {
      Expression::None => {
        self.result.push_str("{}");
        self.clear_state()
      }
      Expression::Sequence(seq) => {
        if let Some(LatexState::NeedWrap) = self.state {
          self.result.push('{');
        }
        for item in seq {
          self.render(item)
        }
        if let Some(LatexState::NeedWrap) = self.state {
          self.result.push('}');
          self.clear_state();
        }
      }
      Expression::Raw(raw) => {
        if raw.is_empty() {
          self.render(Expression::None)
        } else if raw
          .chars()
          .next()
          .map_or(false, |c| c.is_ascii_alphabetic())
        {
          match self.state {
            Some(LatexState::NeedSpace) => self.result.push_str(&format!(" {}", raw)),
            Some(LatexState::NeedWrap) if raw.len() > 1 => {
              self.result.push_str(&format!("{{{}}}", raw))
            }
            _ => self.result.push_str(&raw),
          }
        } else {
          match self.state {
            Some(LatexState::NeedWrap) if raw.len() > 1 => {
              self.result.push_str(&format!("{{{}}}", raw))
            }
            _ => self.result.push_str(&raw),
          }
        }
        self.clear_state()
      }
      Expression::Symbol(symbol) => {
        let leaf = self.symbols.find_str(&symbol);
        let value: String;
        if let Some(val) = leaf.map(Trie::value).flatten() {
          value = val.clone();
        } else {
          value = symbol;
        }
        if value.starts_with('\\') {
          self.result.push_str(&value);
        } else {
          match self.state {
            Some(LatexState::NeedSpace) => self.result.push_str(&format!(" {}", value)),
            _ => self.result.push_str(&value),
          }
        }
        if value
          .chars()
          .last()
          .map_or(false, |c| c.is_ascii_alphabetic())
        {
          self.set_state(LatexState::NeedSpace)
        } else {
          self.clear_state()
        }
      }
      Expression::Function { func, args, .. } => match func.as_str() {
        "abs" => {
          let arg = args.into_iter().next().flatten().unwrap_or(Expression::None);
          self.result.push_str("\\left\\lvert");
          self.set_state(LatexState::NeedSpace);
          self.render(arg);
          self.result.push_str("\\right\\rvert");
          self.set_state(LatexState::NeedSpace);
        },
        "floor" => {
          let arg = args.into_iter().next().flatten().unwrap_or(Expression::None);
          self.result.push_str("\\left\\lfloor");
          self.set_state(LatexState::NeedSpace);
          self.render(arg);
          self.result.push_str("\\right\\rfloor");
          self.set_state(LatexState::NeedSpace);
        },
        "ceil" => {
          let arg = args.into_iter().next().flatten().unwrap_or(Expression::None);
          self.result.push_str("\\left\\lceil");
          self.set_state(LatexState::NeedSpace);
          self.render(arg);
          self.result.push_str("\\right\\rceil");
          self.set_state(LatexState::NeedSpace);
        },
        "norm" => {
          let arg = args.into_iter().next().flatten().unwrap_or(Expression::None);
          self.result.push_str("\\left\\lVert");
          self.set_state(LatexState::NeedSpace);
          self.render(arg);
          self.result.push_str("\\right\\rVert");
          self.set_state(LatexState::NeedSpace);
        },
        "root" => {
          let mut args = args.into_iter().map(|opt| opt.unwrap_or(Expression::None));
          self.result.push_str("\\sqrt[");
          self.render(args.next().unwrap());
          self.result.push_str("]{");
          self.render(args.next().unwrap());
          self.result.push_str("}");
          self.clear_state();
        },
        _func => todo!(),
      },
      Expression::Text { text, font } => {
        let font = font.unwrap_or("".into());
        self.result.push_str(&match font.as_str() {
          "bb" => format!("\\textbf{{{}}}", text),
          "bbb" => format!("\\mathbb{{{}}}", text),
          "cc" => format!("\\mathcal{{{}}}", text),
          "tt" => format!("\\texttt{{{}}}", text),
          "fr" => format!("\\mathfrak{{{}}}", text),
          "sf" => format!("\\textsf{{{}}}", text),
          _ => format!("\\text{{{}}}", text),
        });
        self.clear_state()
      }
      Expression::Sub { .. } => todo!(),
      Expression::Sup { .. } => todo!(),
      Expression::Fraction {
        denominator,
        numerator,
      } => {
        self.result.push_str("\\frac{");
        if let Some(numerator) = numerator {
          self.render(*numerator);
        }
        self.result.push_str("}{");
        if let Some(denominator) = denominator {
          self.render(*denominator);
        }
        self.result.push_str("}");
        self.clear_state()
      }
      Expression::Bracketed { left, right, inner } => {
        let right = right.unwrap_or(":}".into());
        let left = self
          .symbols
          .find_str(&left)
          .map(Trie::value)
          .flatten()
          .map(String::clone)
          .unwrap_or(left);
        let right = self
          .symbols
          .find_str(&right)
          .map(Trie::value)
          .flatten()
          .map(String::clone)
          .unwrap_or(right);
        self.result.push_str(&left);
        if left
          .chars()
          .last()
          .map_or(false, |c| c.is_ascii_alphabetic())
        {
          self.set_state(LatexState::NeedSpace);
        }
        self.render(*inner);
        self.result.push_str(&right);
        if right
          .chars()
          .last()
          .map_or(false, |c| c.is_ascii_alphabetic())
        {
          self.set_state(LatexState::NeedSpace);
        }
      }
      Expression::Matrix { .. } => todo!(),
      Expression::Token(_) => panic!("unexpected token in parsed expression"),
    }
  }

  fn result(&self) -> String {
    self.result.clone()
  }
}

pub fn render(expr: Expression, output_format: crate::OutputFormat) -> String {
  let mut renderer: Box<dyn Renderer> = Box::new(match output_format {
    crate::OutputFormat::Latex => LatexRenderer::new(),
  });
  renderer.render(expr);
  renderer.result()
}

#[cfg(test)]
mod latex_tests {
  use super::*;

  use crate::parse::parse;
  use crate::tokens::tokenize;

  fn lren(input: &str) -> String {
    let expr = parse(tokenize(input, vec![]));
    render(expr, crate::OutputFormat::Latex)
  }

  #[test]
  fn one_plus_one() {
    assert_eq!(lren("1+1"), "1+1".to_owned());
  }

  #[test]
  fn simple_func() {
    assert_eq!(
      lren("f(x) = 2(x + 2)"),
      "f\\left(x\\right)=2\\left(x+2\\right)".to_owned()
    );
    assert_eq!(
      lren("(:\"magic\""),
      "\\left\\lang\\text{magic}\\right."
    )
  }
}
