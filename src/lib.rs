mod parse;
mod render;
mod tokens;
mod trie;

pub enum OutputFormat {
  Latex,
}

/// Converts input string to specified format
/// ```
/// use am_parse::{convert, OutputFormat};
/// assert_eq!(convert("1+1".into(), OutputFormat::Latex, vec![]), "1+1");
/// assert_eq!(convert("fx = 1/2".into(), OutputFormat::Latex, vec!["f"]), "f{\\left(x\\right)}=\\frac{1}{2}");
/// ```
pub fn convert(input: String, output_format: OutputFormat, custom_functions: Vec<&str>) -> String {
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
