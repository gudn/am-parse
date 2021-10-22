use wasm_bindgen::prelude::*;

mod parse;
mod render;
mod tokens;
mod trie;

#[wasm_bindgen]
pub enum OutputFormat {
  Latex,
}

#[wasm_bindgen]
pub fn convert(input: String, output_format: OutputFormat, custom_functions: String) -> String {
  let custom_functions = if custom_functions.is_empty() {
    Vec::new()
  } else {
    custom_functions.split(' ').collect()
  };
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
      convert("blabla".into(), OutputFormat::Latex, "".into()),
      "blabla".to_owned()
    );
  }
}
