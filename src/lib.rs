use wasm_bindgen::prelude::*;

mod trie;
mod tokens;
mod render;
mod parse;

#[wasm_bindgen]
pub enum OutputFormat {
  Latex,
}

#[wasm_bindgen]
pub fn convert(input: String, _output_format: OutputFormat) -> String {
  let tokens = tokens::tokenize(&input);
  let _tree = parse::parse(tokens);
  unimplemented!()
}
