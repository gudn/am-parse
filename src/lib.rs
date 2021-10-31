mod parse;
mod render;
mod tokens;
mod trie;

pub enum OutputFormat {
  Latex,
}

pub fn convert(
  input: String,
  output_format: OutputFormat,
  custom_functions: Vec<&str>,
) -> String {
  let tokens = tokens::tokenize(&input, custom_functions);
  let expr = parse::parse(tokens);
  render::render(expr, output_format)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn blabla() {
    assert_eq!(
      convert("blabla".into(), OutputFormat::Latex, vec![]),
      "blabla".to_owned()
    );
  }
}
