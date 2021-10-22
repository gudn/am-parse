use std::collections::HashMap;
use std::str::Chars;

pub struct Trie<T> {
  value: Option<T>,
  children: HashMap<char, Trie<T>>,
}

impl<T> Trie<T> {
  pub fn new() -> Trie<T> {
    Trie {
      value: None,
      children: HashMap::new(),
    }
  }

  pub fn insert(&mut self, key: &str, value: T) {
    let trie = Trie::find_or_create(self, key.chars());
    trie.value = Some(value)
  }

  fn find_or_create<'a>(curr: &'a mut Trie<T>, mut chars: Chars) -> &'a mut Trie<T> {
    if let Some(c) = chars.next() {
      let child = curr.children.entry(c).or_insert_with(Trie::new);
      Trie::find_or_create(child, chars)
    } else {
      curr
    }
  }

  pub fn find(&self, key: char) -> Option<&Trie<T>> {
    self.children.get(&key)
  }

  pub fn find_str(&self, key: &str) -> Option<&Trie<T>> {
    let mut curr = self;
    for c in key.chars() {
      curr = curr.find(c)?;
    }
    Some(curr)
  }

  pub fn is_value(&self) -> bool {
    self.value.is_some()
  }

  pub fn value(&self) -> Option<&T> {
    self.value.as_ref()
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn new_create_empty() {
    let root: Trie<()> = Trie::new();
    assert!(root.value().is_none())
  }

  #[test]
  fn insert_create_new_nodes() {
    let mut root = Trie::new();
    root.insert("", ());
    root.insert("abc", ());
    root.insert("aba", ());
    assert!(root.is_value());
    assert_eq!(root.children.len(), 1);
    let a = root.children.get(&'a').expect("'a' is None");
    let ab = a.children.get(&'b').expect("'b' is None");
    assert_eq!(ab.children.len(), 2);
  }

  #[test]
  fn find_str() {
    let mut root = Trie::new();
    root.insert("", 1);
    root.insert("abc", 2);
    root.insert("aba", 3);
    assert_eq!(root.find_str("").unwrap().value(), Some(&1));
    assert_eq!(root.find_str("ab").unwrap().value(), None);
    assert_eq!(root.find_str("abc").unwrap().value(), Some(&2));
    assert_eq!(root.find_str("aba").unwrap().value(), Some(&3));
  }
}
