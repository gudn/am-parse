#[derive(PartialEq, Eq, Debug)]
pub enum Token {
  Raw(String),
  Text(String),
  Font(String),
  LeftBracket(String),
  RightBracket(String),
  BracketFunction(String),
  Function(String, u32),
  Symbol(String),
  Delimiter(String),
  Operator(String),
  Subsup(String),
  Whitespace,
}
