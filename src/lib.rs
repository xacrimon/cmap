mod codegen;

use proc_macro::TokenStream;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{Expr, Type};
use syn::{Ident, LitByteStr, Token, parse_macro_input};

struct Map {
    fn_name: Ident,
    ty: Type,
    pairs: Punctuated<Case, Token![,]>,
}

impl Parse for Map {
    fn parse(input: ParseStream) -> Result<Self> {
        let fn_name = input.parse()?;
        input.parse::<Token![,]>()?;
        let ty = input.parse::<Type>()?;
        input.parse::<Token![,]>()?;
        let pairs = Punctuated::parse_terminated(input)?;

        Ok(Map { fn_name, ty, pairs })
    }
}

struct Case {
    key: LitByteStr,
    value: Expr,
}

impl Parse for Case {
    fn parse(input: ParseStream) -> Result<Self> {
        let key: LitByteStr = input.parse()?;
        input.parse::<Token![=>]>()?;
        let value: Expr = input.parse()?;

        Ok(Case { key, value })
    }
}

#[proc_macro]
pub fn map(input: TokenStream) -> TokenStream {
    let Map { fn_name, ty, pairs } = parse_macro_input!(input as Map);

    let pairs = pairs
        .into_iter()
        .map(|Case { key, value }| {
            let key = key.value();
            codegen::Pair { key, value }
        })
        .collect::<Vec<_>>();

    let expanded = codegen::generate_fn(pairs, &fn_name, &ty);

    TokenStream::from(expanded)
}
