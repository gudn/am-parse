use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub enum OutputFormat {
  Latex,
}

#[wasm_bindgen]
pub fn convert(_input: String, _output_format: OutputFormat) -> String {
  unimplemented!()
}
