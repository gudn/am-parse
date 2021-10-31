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
      if let (Some(key), Some(value)) = (key, value) {
        symbols.insert(key, value.into());
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

  fn wrap(&mut self, expr: Expression) {
    self.result.push('{');
    self.clear_state();
    self.render(expr);
    self.result.push('}');
    self.clear_state();
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
          self.wrap(Expression::Sequence(seq))
        } else {
          for item in seq {
            self.render(item)
          }
        }
      }
      Expression::Raw(raw) => {
        if let Some(LatexState::NeedWrap) = self.state {
          if raw.len() == 1 {
            if self
              .result
              .chars()
              .last()
              .map_or(false, |c| c.is_ascii_alphabetic())
            {
              // HACK
              self.set_state(LatexState::NeedSpace);
            } else {
              self.clear_state();
            }
          }
        }
        if raw.is_empty() {
          self.render(Expression::None)
        } else if let Some(LatexState::NeedWrap) = self.state {
          self.wrap(Expression::Raw(raw));
        } else if raw
          .chars()
          .next()
          .map_or(false, |c| c.is_ascii_alphabetic())
        {
          if let Some(LatexState::NeedSpace) = self.state {
            self.result.push(' ');
          }
          self.result.push_str(&raw);
        } else {
          self.result.push_str(&raw);
        }
        self.clear_state()
      }
      Expression::Symbol(symbol) => {
        if let Some(LatexState::NeedWrap) = self.state {
          self.wrap(Expression::Symbol(symbol));
        } else {
          let leaf = self.symbols.find_str(&symbol);
          let value = if let Some(val) = leaf.map(Trie::value).flatten() {
            val.clone()
          } else {
            symbol
          };
          if value.starts_with('\\') {
            self.result.push_str(&value);
          } else {
            if let Some(LatexState::NeedSpace) = self.state {
              self.result.push(' ');
            }
            self.result.push_str(&value);
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
      }
      Expression::Function {
        func,
        args,
        mut extra,
      } => {
        if let Some(LatexState::NeedWrap) = self.state {
          self.wrap(Expression::Function { func, args, extra });
        } else {
          match func.as_str() {
            "abs" => {
              let arg = args
                .into_iter()
                .next()
                .flatten()
                .unwrap_or(Expression::None);
              self.result.push_str("\\left\\lvert");
              self.set_state(LatexState::NeedSpace);
              self.render(arg);
              self.result.push_str("\\right\\rvert");
              self.set_state(LatexState::NeedSpace);
            }
            "floor" => {
              let arg = args
                .into_iter()
                .next()
                .flatten()
                .unwrap_or(Expression::None);
              self.result.push_str("\\left\\lfloor");
              self.set_state(LatexState::NeedSpace);
              self.render(arg);
              self.result.push_str("\\right\\rfloor");
              self.set_state(LatexState::NeedSpace);
            }
            "ceil" => {
              let arg = args
                .into_iter()
                .next()
                .flatten()
                .unwrap_or(Expression::None);
              self.result.push_str("\\left\\lceil");
              self.set_state(LatexState::NeedSpace);
              self.render(arg);
              self.result.push_str("\\right\\rceil");
              self.set_state(LatexState::NeedSpace);
            }
            "norm" => {
              let arg = args
                .into_iter()
                .next()
                .flatten()
                .unwrap_or(Expression::None);
              self.result.push_str("\\left\\lVert");
              self.set_state(LatexState::NeedSpace);
              self.render(arg);
              self.result.push_str("\\right\\rVert");
              self.set_state(LatexState::NeedSpace);
            }
            "root" => {
              let mut args = args.into_iter().map(|opt| opt.unwrap_or(Expression::None));
              self.result.push_str("\\sqrt[");
              self.render(args.next().unwrap());
              self.result.push_str("]{");
              self.render(args.next().unwrap());
              self.result.push('}');
              self.clear_state();
            }
            "log" => {
              let mut args = args.into_iter().map(|opt| opt.unwrap_or(Expression::None));
              self.result.push_str("\\log_");
              self.set_state(LatexState::NeedWrap);
              self.render(args.next().unwrap());
              self.set_state(LatexState::NeedWrap);
              self.render(args.next().unwrap());
            }
            "gcd" | "lcm " => {
              let mut args = args.into_iter().map(|opt| opt.unwrap_or(Expression::None));
              self.result.push('\\');
              self.result.push_str(&func);
              self.result.push('{');
              self.clear_state();
              self.render(args.next().unwrap());
              self.result.push(',');
              self.clear_state();
              self.render(args.next().unwrap());
              self.result.push('}');
              self.clear_state();
            }
            "ubrace" => {
              self.result.push_str("\\underbrace{");
              if let Some(arg) = args.into_iter().next().flatten() {
                self.clear_state();
                self.render(arg);
              }
              self.result.push('}');
              self.clear_state();
              if let Some(sub) = extra.sub {
                if let Expression::Sub { sub, .. } = *sub {
                  let sub = sub.unwrap_or_else(|| Box::new(Expression::None));
                  self.result.push('_');
                  self.set_state(LatexState::NeedWrap);
                  self.render(*sub);
                } else {
                  panic!("expected Expression::Sub");
                }
              }
            }
            "obrace" => {
              self.result.push_str("\\overbrace{");
              if let Some(arg) = args.into_iter().next().flatten() {
                self.clear_state();
                self.render(arg);
              }
              self.result.push('}');
              self.clear_state();
              if let Some(sup) = extra.sup {
                if let Expression::Sup { sup, .. } = *sup {
                  let sup = sup.unwrap_or_else(|| Box::new(Expression::None));
                  self.result.push('^');
                  self.set_state(LatexState::NeedWrap);
                  self.render(*sup);
                } else {
                  panic!("expected Expression::Sub");
                }
              }
            }
            _ => {
              let leaf = self.symbols.find_str(&func);
              let value = if let Some(val) = leaf.map(Trie::value).flatten() {
                val.clone()
              } else {
                func
              };
              if value.starts_with('\\') {
                self.result.push_str(&value);
              } else {
                if let Some(LatexState::NeedSpace) = self.state {
                  self.result.push(' ');
                }
                self.result.push_str(&value);
              }
              if let Some(sub) = extra.sub {
                if let Expression::Sub { sub, .. } = *sub {
                  let sub = sub.unwrap_or_else(|| Box::new(Expression::None));
                  self.result.push('_');
                  self.set_state(LatexState::NeedWrap);
                  self.render(*sub);
                } else {
                  panic!("expected Expression::Sub");
                }
              }
              if let Some(sup) = extra.sup {
                if let Expression::Sup { sup, .. } = *sup {
                  let sup = sup.unwrap_or_else(|| Box::new(Expression::None));
                  self.result.push('^');
                  self.set_state(LatexState::NeedWrap);
                  self.render(*sup);
                } else {
                  panic!("expected Expression::Sup");
                }
              } else {
                while extra.derivative_level > 0 {
                  extra.derivative_level -= 1;
                  self.result.push('\'');
                }
              }
              for arg in args {
                self.set_state(LatexState::NeedWrap);
                self.render(arg.unwrap_or(Expression::None));
              }
            }
          }
        }
      }
      Expression::Text { text, font } => {
        let font = font.unwrap_or_default();
        self.result.push_str(match font.as_str() {
          "bb" => "\\mathbf{{",
          "bbb" => "\\mathbb{{",
          "cc" => "\\mathcal{{",
          "tt" => "\\mathtt{{",
          "fr" => "\\mathfrak{{",
          "sf" => "\\mathsf{{",
          _ => "\\text{",
        });
        self.result.push_str(&text);
        self
          .result
          .push_str(if font.is_empty() { "}" } else { "}}" });
        self.clear_state()
      }
      Expression::Sub { base, sub } => {
        if let Some(LatexState::NeedWrap) = self.state {
          self.wrap(Expression::Sub { base, sub });
        } else {
          let base = base.unwrap_or_else(|| Box::new(Expression::None));
          let sub = sub.unwrap_or_else(|| Box::new(Expression::None));
          self.set_state(LatexState::NeedWrap);
          self.render(*base);
          self.result.push('_');
          self.set_state(LatexState::NeedWrap);
          self.render(*sub);
        }
      }
      Expression::Sup { base, sup } => {
        if let Some(LatexState::NeedWrap) = self.state {
          self.wrap(Expression::Sup { base, sup });
        } else {
          let base = base.unwrap_or_else(|| Box::new(Expression::None));
          let sup = sup.unwrap_or_else(|| Box::new(Expression::None));
          self.set_state(LatexState::NeedWrap);
          self.render(*base);
          self.result.push('^');
          self.set_state(LatexState::NeedWrap);
          self.render(*sup);
        }
      }
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
        self.result.push('}');
        self.clear_state()
      }
      Expression::Bracketed { left, right, inner } => {
        if let Some(LatexState::NeedWrap) = self.state {
          self.wrap(Expression::Bracketed { left, right, inner })
        } else {
          let right = right.unwrap_or_else(|| ":}".into());
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
      }
      Expression::Matrix { left, right, items } => {
        let render_row = |this: &mut LatexRenderer, row: Vec<Expression>| {
          let mut row = row.into_iter();
          if let Some(first) = row.next() {
            this.render(first);
          }
          for elem in row {
            this.result.push('&');
            this.render(elem);
          }
        };
        let render_items = |this: &mut LatexRenderer| {
          let mut rows = items.into_iter();
          if let Some(first) = rows.next() {
            render_row(this, first);
          }
          for row in rows {
            this.result.push_str("\\\\");
            render_row(this, row);
          }
        };
        let right = right.unwrap_or_else(|| ":}".into());
        match (left.as_str(), right.as_str()) {
          ("(", ")") => {
            self.result.push_str("\\begin{pmatrix}");
            render_items(self);
            self.result.push_str("\\end{pmatrix}");
          }
          ("[", "]") => {
            self.result.push_str("\\begin{bmatrix}");
            render_items(self);
            self.result.push_str("\\end{bmatrix}");
          }
          ("{", "}") => {
            self.result.push_str("\\begin{Bmatrix}");
            render_items(self);
            self.result.push_str("\\end{Bmatrix}");
          }
          ("{", ":}") => {
            self.result.push_str("\\begin{cases}");
            render_items(self);
            self.result.push_str("\\end{cases}");
          }
          ("{:", "}") => {
            self.result.push_str("\\begin{rcases}");
            render_items(self);
            self.result.push_str("\\end{rcases}");
          }
          ("|:", ":|") => {
            self.result.push_str("\\begin{vmatrix}");
            render_items(self);
            self.result.push_str("\\end{vmatrix}");
          }
          ("{:", ":}") => {
            self.result.push_str("\\begin{matrix}");
            render_items(self);
            self.result.push_str("\\end{matrix}");
          }
          (_, _) => {
            self.render(Expression::Symbol(left));
            self.result.push_str("\\begin{matrix}");
            render_items(self);
            self.result.push_str("\\end{matrix}");
            self.render(Expression::Symbol(right));
          }
        }
      }
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
    assert_eq!(lren("1+1"), "1+1");
  }

  #[test]
  fn simple_func() {
    assert_eq!(
      lren("f(x) = 2(x + 2)"),
      "f\\left(x\\right)=2\\left(x+2\\right)"
    );
    assert_eq!(lren("(:\"magic\""), "\\left\\lang\\text{magic}\\right.")
  }

  #[test]
  fn simple_subsup() {
    assert_eq!(lren("1^ 2+3"), "1^{2+3}");
    assert_eq!(lren("1_2^3_2"), "{{1_2}^3}_2");
    assert_eq!(lren("1/ 2 ^ 3"), "\\frac{1}{2}^3");
    assert_eq!(lren("1 / 2^ 3"), "\\frac{1}{2^3}");
  }

  #[test]
  fn some_funcs() {
    assert_eq!(lren("sinx"), "\\sin x");
    assert_eq!(lren("sin' x^2 = 2xcos x^2"), "\\sin'{x^2}=2x\\cos{x^2}");
    assert_eq!(lren("cos abra / 2"), "\\frac{\\cos{abra}}{2}");
  }

  #[test]
  fn simple_cases() {
    assert_eq!(lren("{x=5;x=6:}"), "\\begin{cases}x=5\\\\x=6\\end{cases}");
    assert_eq!(
      lren("(x=5;x=6:)"),
      "\\left(\\begin{matrix}x=5\\\\x=6\\end{matrix}\\right\\rang"
    );
  }

  #[test]
  fn blabla() {
    assert_eq!(lren("blabla"), "blabla");
  }

  #[test]
  fn overbrace_underbrace() {
    assert_eq!(lren("obrace^y x"), "\\overbrace{x}^y");
    assert_eq!(lren("ubrace_y x"), "\\underbrace{x}_y");
  }
}
