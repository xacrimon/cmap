mod codegen;

use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::{Pair, Punctuated};
use syn::spanned::Spanned;
use syn::{Expr, Ident, Lit, LitByteStr, LitInt, Token, Type, Visibility, parse_macro_input};

struct Map {
    fn_name: Ident,
    pairs: Punctuated<Case, Token![,]>,
}

impl Parse for Map {
    fn parse(input: ParseStream) -> Result<Self> {
        let fn_name = input.parse()?;
        input.parse::<Token![,]>()?;
        let pairs = Punctuated::parse_terminated(input)?;

        Ok(Map { fn_name, pairs })
    }
}

struct Case {
    key: LitByteStr,
    value: LitInt,
}

impl Parse for Case {
    fn parse(input: ParseStream) -> Result<Self> {
        let key: LitByteStr = input.parse()?;
        input.parse::<Token![=>]>()?;
        let value: LitInt = input.parse()?;

        Ok(Case { key, value })
    }
}

#[proc_macro]
pub fn map(input: TokenStream) -> TokenStream {
    let Map { fn_name, pairs } = parse_macro_input!(input as Map);

    let mut pairs = pairs
        .into_iter()
        .map(|Case { key, value }| {
            let key = key.value();
            let value = value.base10_parse::<i32>().unwrap();
            codegen::Pair { key, value }
        })
        .collect::<Vec<_>>();

    let expanded = codegen::generate_fn(pairs, &fn_name);

    TokenStream::from(expanded)
}
