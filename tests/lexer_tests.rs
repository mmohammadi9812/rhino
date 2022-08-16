// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.


extern crate rhino;
use rhino::{lexer::{*, TokenEnum::*}, interner::get_local_interner};

fn new_token(token: TokenEnum, value: &str) -> Token {
    Token::new(
        &get_local_interner(),
        token,
        value,
        Location {
            column: -1,
            row: -1,
            absolute: -1,
        },
    )
}

#[test]
fn simple() {
    let mut lexer = Lexer::new("test 2 + 3".chars());

    assert_eq!(*lexer.next(), new_token(NAME, "test"));
    assert_eq!(*lexer.next(), new_token(NUMBER, "2"));
    assert_eq!(*lexer.next(), new_token(OPERATOR, "+"));
    assert_eq!(*lexer.next(), new_token(NUMBER, "3"));
}
#[test]
fn let_bind() {
    let mut lexer = Lexer::new(
        r"let
test = 2 + 3
in test"
            .chars(),
    );

    assert_eq!(*lexer.next(), new_token(LET, "let"));
    assert_eq!(*lexer.next(), new_token(LBRACE, "{"));
    assert_eq!(*lexer.next(), new_token(NAME, "test"));
    assert_eq!(*lexer.next(), new_token(EQUALSSIGN, "="));
    assert_eq!(*lexer.next(), new_token(NUMBER, "2"));
    assert_eq!(*lexer.next(), new_token(OPERATOR, "+"));
    assert_eq!(*lexer.next(), new_token(NUMBER, "3"));
}
