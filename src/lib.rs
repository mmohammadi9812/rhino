// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

#![crate_type = "bin"]
#![feature(box_syntax)]
#![cfg_attr(test, feature(test))]

pub mod builtins;
pub mod compiler;
pub mod core;
pub mod deriving;
pub mod graph;
pub mod infix;
pub mod interner;
pub mod lambda_lift;
pub mod lexer;
#[macro_use] pub mod module;
pub mod parser;
pub mod renamer;
#[cfg(not(test))]
mod repl;
pub mod scoped_map;
pub mod typecheck;
pub mod types;
pub mod vm;
