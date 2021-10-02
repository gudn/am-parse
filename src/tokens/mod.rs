use crate::trie::Trie;

mod token;
mod wrapper;
use wrapper::InputWrapper;
pub use token::Token;

#[derive(Clone, Copy)]
enum SymbolType {
  Font,
  BracketFunction,
  Function(u32),
  Delimiter,
  Symbol,
  Operator,
  LeftBracket,
  RightBracket,
  Subsup,
}

fn load_symbols_list() -> Trie<SymbolType> {
  let list = std::include_str!("symbols.toml");
  let mut root = Trie::new();
  let mut curr_type = SymbolType::Symbol;
  for line in list.lines().map(|line| line.trim()) {
    if line.starts_with('[') && line.ends_with(']') {
      curr_type = match line {
        "[font]" => SymbolType::Font,
        "[function.bracket]" => SymbolType::BracketFunction,
        "[function.1]" => SymbolType::Function(1),
        "[function.2]" => SymbolType::Function(2),
        "[symbol]" => SymbolType::Symbol,
        "[operator]" => SymbolType::Operator,
        "[left_bracket]" => SymbolType::LeftBracket,
        "[right_bracket]" => SymbolType::RightBracket,
        "[delimiter]" => SymbolType::Delimiter,
        "[subsup]" => SymbolType::Subsup,
        _ => SymbolType::Symbol,
      };
    } else {
      root.insert(line, curr_type);
    }
  }
  root
}

fn match_number(input: &mut InputWrapper) -> Option<Token> {
  let mut number = String::new();
  let mut was_dot = false;
  let mark = input.mark();
  match input.take()? {
    '-' => number.push('-'),
    '.' => {
      was_dot = true;
      number.push('.')
    }
    c if c.is_digit(10) => number.push(c),
    _ => {
      input.reset(mark);
      return None;
    }
  }
  while let Some(c) = input.peek() {
    match c {
      '.' if !was_dot => {
        was_dot = true;
        number.push(input.take().expect("expect char `c`"))
      }
      c if c.is_digit(10) => number.push(input.take().expect("expect char `c`")),
      _ => break,
    }
  }
  if number == "." || number == "-" {
    input.reset(mark);
    None
  } else {
    Some(Token::Raw(number))
  }
}

fn match_text(input: &mut InputWrapper) -> Option<Token> {
  let mut content = String::new();
  if let Some('"') = input.peek() {
  } else {
    return None;
  }
  input.take().expect("expected double-quote");
  while let Some(c) = input.take() {
    if c == '"' {
      break;
    } else {
      content.push(c);
    }
  }
  Some(Token::Text(content))
}

fn match_symbol(input: &mut InputWrapper, symbols: &Trie<SymbolType>) -> Option<Token> {
  let mut last_match = symbols;
  let mut curr = symbols;
  let mut buffer = String::new();
  let mut mark = input.mark();
  while let Some(c) = input.peek() {
    if c == '\\' {
      break;
    }
    if let Some(child) = curr.find(c) {
      buffer.push(input.take().expect("expected `c`"));
      curr = child;
      if child.is_value() {
        mark = input.mark();
        last_match = child;
      }
    } else {
      break;
    }
  }
  input.reset(mark);
  if let Some(value) = last_match.value() {
    Some(match *value {
      SymbolType::BracketFunction => Token::BracketFunction(buffer),
      SymbolType::Font => Token::Font(buffer),
      SymbolType::Function(arg) => Token::Function(buffer, arg),
      SymbolType::LeftBracket => Token::LeftBracket(buffer),
      SymbolType::RightBracket => Token::RightBracket(buffer),
      SymbolType::Symbol => Token::Symbol(buffer),
      SymbolType::Operator => Token::Operator(buffer),
      SymbolType::Delimiter => Token::Delimiter(buffer),
      SymbolType::Subsup => Token::Subsup(buffer),
    })
  } else {
    None
  }
}

struct Simplifier {
  data: Vec<Token>,
}

impl Simplifier {
  fn new() -> Simplifier {
    Simplifier { data: Vec::new() }
  }

  fn push(&mut self, value: Token) {
    match value {
      Token::Whitespace => {
        if let Some(Token::Whitespace) = self.data.last() {
        } else {
          self.data.push(value);
        }
      }
      Token::Raw(c) => {
        if let Some(Token::Raw(t)) = self.data.last_mut() {
          t.push_str(&c);
        } else {
          self.data.push(Token::Raw(c));
        }
      }
      _ => self.data.push(value),
    }
  }
}

impl From<Simplifier> for Vec<Token> {
  fn from(value: Simplifier) -> Vec<Token> {
    value.data
  }
}

pub fn tokenize(input: &str) -> Vec<Token> {
  let symbols = load_symbols_list();
  let mut input = InputWrapper::new(input.trim().into());
  let mut tokens = Simplifier::new();
  while let Some(c) = input.peek() {
    if let Some(token) = match_number(&mut input) {
      tokens.push(token);
    } else if let Some(token) = match_text(&mut input) {
      tokens.push(token);
    } else if c.is_whitespace() {
      input.take().expect("expected space");
      tokens.push(Token::Whitespace);
    } else if c == '\\' {
      input.take().expect("expeted backslash");
      if let Some(c) = input.take() {
        tokens.push(Token::Raw(c.into()));
      }
    } else if let Some(token) = match_symbol(&mut input, &symbols) {
      tokens.push(token);
    } else {
      tokens.push(Token::Raw(input.take().expect("expected `c`").into()));
    }
  }
  tokens.into()
}

#[cfg(test)]
mod tests {
  use super::*;

  fn raw(value: &str) -> Token {
    Token::Raw(value.into())
  }

  fn text(value: &'static str) -> Token {
    Token::Text(value.into())
  }

  #[test]
  fn load_all_symbols_from_list() {
    let symbols = load_symbols_list();
    assert!(!symbols.is_value());
    let list = std::include_str!("symbols.toml");
    for line in list.lines().map(|line| line.trim()) {
      if line.starts_with('[') && line.ends_with(']') {
        continue;
      } else {
        let symbol = symbols.find_str(line);
        if let Some(trie) = symbol {
          assert!(trie.is_value())
        } else {
          panic!("symbol not found")
        }
      }
    }
  }

  #[test]
  fn parse_number() {
    let input: String = "123.-32.3423.223ab".into();
    let mut three_numbers = InputWrapper::new(input.clone());
    assert_eq!(super::match_number(&mut three_numbers), Some(raw("123.")));
    assert_eq!(match_number(&mut three_numbers), Some(raw("-32.3423")));
    let m = three_numbers.mark();
    assert_eq!(match_number(&mut three_numbers), Some(raw(".223")));
    three_numbers.reset(m);
    assert_eq!(match_number(&mut three_numbers), Some(raw(".223")));
    assert_eq!(three_numbers.take(), Some('a'));
    assert_eq!(three_numbers.take(), Some('b'));
    assert_eq!(tokenize(&input), vec![raw(&input)]);
  }

  #[test]
  fn parse_text() {
    let input: String = r#""abra 123 arba"   "some"#.into();
    let mut some_string = InputWrapper::new(input.clone());
    assert_eq!(match_text(&mut some_string), Some(text("abra 123 arba")));
    assert_eq!(match_text(&mut some_string), None);
    assert_eq!(some_string.take(), Some(' '));
    assert_eq!(some_string.take(), Some(' '));
    assert_eq!(some_string.take(), Some(' '));
    assert_eq!(match_text(&mut some_string), Some(text("some")));
    assert_eq!(
      tokenize(&input),
      vec![text("abra 123 arba"), Token::Whitespace, text("some"),]
    );
  }

  #[test]
  fn parse_symbol() {
    let symbols = load_symbols_list();
    let input: String = "sincos root(:sum+-+\\)".into();
    let mut some_symbols = InputWrapper::new(input.clone());
    assert_eq!(
      match_symbol(&mut some_symbols, &symbols),
      Some(Token::Function("sin".into(), 1))
    );
    assert_eq!(
      match_symbol(&mut some_symbols, &symbols),
      Some(Token::Function("cos".into(), 1))
    );
    assert_eq!(some_symbols.take(), Some(' '));
    assert_eq!(
      match_symbol(&mut some_symbols, &symbols),
      Some(Token::Function("root".into(), 2))
    );
    assert_eq!(
      match_symbol(&mut some_symbols, &symbols),
      Some(Token::LeftBracket("(:".into()))
    );
    assert_eq!(
      match_symbol(&mut some_symbols, &symbols),
      Some(Token::Symbol("sum".into()))
    );
    assert_eq!(
      match_symbol(&mut some_symbols, &symbols),
      Some(Token::Operator("+-".into()))
    );
    assert_eq!(
      match_symbol(&mut some_symbols, &symbols),
      Some(Token::Operator("+".into()))
    );
    assert_eq!(match_symbol(&mut some_symbols, &symbols), None);
    assert_eq!(some_symbols.take(), Some('\\'));
    assert_eq!(some_symbols.take(), Some(')'));
    assert_eq!(
      tokenize(&input),
      vec![
        Token::Function("sin".into(), 1),
        Token::Function("cos".into(), 1),
        Token::Whitespace,
        Token::Function("root".into(), 2),
        Token::LeftBracket("(:".into()),
        Token::Symbol("sum".into()),
        Token::Operator("+-".into()),
        Token::Operator("+".into()),
        raw(")")
      ]
    )
  }

  #[test]
  fn tokenize_function_definition() {
    let input = "f(x) = 2x + 1";
    assert_eq!(
      tokenize(input),
      vec![
        raw("f"),
        Token::LeftBracket("(".into()),
        raw("x"),
        Token::RightBracket(")".into()),
        Token::Whitespace,
        Token::Operator("=".into()),
        Token::Whitespace,
        raw("2x"),
        Token::Whitespace,
        Token::Operator("+".into()),
        Token::Whitespace,
        raw("1")
      ]
    )
  }

  #[test]
  fn tokenize_complex_expression() {
    let input = "sum_(i=1)^n i^3=((n(n+1))/2)^2";
    assert_eq!(
      tokenize(input),
      vec![
        Token::Symbol("sum".into()),
        Token::Subsup("_".into()),
        Token::LeftBracket("(".into()),
        raw("i"),
        Token::Operator("=".into()),
        raw("1"),
        Token::RightBracket(")".into()),
        Token::Subsup("^".into()),
        raw("n"),
        Token::Whitespace,
        raw("i"),
        Token::Subsup("^".into()),
        raw("3"),
        Token::Operator("=".into()),
        Token::LeftBracket("(".into()),
        Token::LeftBracket("(".into()),
        raw("n"),
        Token::LeftBracket("(".into()),
        raw("n"),
        Token::Operator("+".into()),
        raw("1"),
        Token::RightBracket(")".into()),
        Token::RightBracket(")".into()),
        Token::Operator("/".into()),
        raw("2"),
        Token::RightBracket(")".into()),
        Token::Subsup("^".into()),
        raw("2"),
      ]
    )
  }

  #[test]
  fn simplifier() {
    let input = "abra   + 12r_0";
    assert_eq!(
      tokenize(&input),
      vec![
        raw("abra"),
        Token::Whitespace,
        Token::Operator("+".into()),
        Token::Whitespace,
        raw("12r"),
        Token::Subsup("_".into()),
        raw("0")
      ]
    );
  }
}
