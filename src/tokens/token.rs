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

impl crate::render::Render for Token {
  fn render(&self, _: crate::OutputFormat) -> String {
    unimplemented!()
  }
}
