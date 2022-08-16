// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

extern crate rhino;
use rhino::scoped_map::ScopedMap;

#[test]
fn test() {
    let mut map = ScopedMap::new();
    map.insert("a", 0);
    map.insert("b", 1);
    map.enter_scope();
    assert_eq!(map.find(&"a"), Some(&0));
    assert_eq!(map.find(&"b"), Some(&1));
    assert_eq!(map.find(&"c"), None);
    map.insert("a", 1);
    map.insert("c", 2);
    assert_eq!(map.find(&"a"), Some(&1));
    assert_eq!(map.find(&"c"), Some(&2));
    map.exit_scope();
    assert_eq!(map.find(&"a"), Some(&0));
    assert_eq!(map.find(&"c"), None);
}
