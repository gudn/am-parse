# am-parse

Simple library for converting asciimath to other formats

## Usage

``` rust
use am_parse::{convert, OutputFormat};

fn main() {
  println!("{}", convert("1/2", OutputFormat::Latex, vec![]));
}
```

`convert` accepts three arguments:
1. asciimath input string
2. output format. Currently supports only Latex
3. Custom functions list. This is list of user-defined functions, like `f`, `g`
   and others. This will be parsed as brace functions.

## AsciiMath dialect

This is not original [AsciiMath](http://asciimath.org). Some symbols is not
included (like `TT`, `|--`, etc); spaces is important -- they split input into
blocks. For example, `1+2/3` renders to `1+\frac{2}{3}`, but `1+2 / 3` renders
to `\frac{1+2}{3}`. This works with functions arguments, fractions, superscripts
and subscripts. Also it includes brace functions: they are enforced to be Matrix
or expression in brackets.

### Examples
- `root 3 x /4` -> `\frac{\sqrt[3]{x}}{4}`
- `sin 3*x` -> `\sin{3\cdot x}`, `sin3*x` -> `\sin3\cdot x`
- `fr"text"`-> `\mathfrak{text}`
