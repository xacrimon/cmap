use proc_macro2::{Ident, Literal, Span, TokenStream};
use quote::{ToTokens, quote};
use std::collections::BTreeMap;

#[derive(Clone)]
pub struct Pair {
    pub key: Vec<u8>,
    pub value: i32,
}

pub fn generate_fn(pairs: Vec<Pair>, fn_name: &Ident) -> TokenStream {
    let key = Ident::new("bytes", Span::call_site());
    let expr = generate_expr(pairs, &key);

    quote! {
        #[inline(never)]
        fn #fn_name(#key: &[u8]) -> Option<i32> {
            Some(#expr)
        }
    }
}

fn generate_expr(mut pairs: Vec<Pair>, key: &Ident) -> TokenStream {
    pairs.sort_by_key(|pair| pair.key.len());

    let mut branches = Vec::new();
    while !pairs.is_empty() {
        let len = pairs[0].key.len();
        let branch_pairs = pairs
            .iter()
            .take_while(|pair| pair.key.len() == len)
            .cloned()
            .collect::<Vec<_>>();

        pairs.drain(0..branch_pairs.len()).for_each(|_| {});
        let expr = generate_expr_for_arm(branch_pairs, key, len);
        let arm = quote! { #len => #expr, };
        branches.push(arm);
    }

    quote! {
        match #key.len() {
            #(#branches)*
            _ => return None,
        }
    }
}

fn generate_expr_for_arm(mut pairs: Vec<Pair>, key: &Ident, len: usize) -> TokenStream {
    pairs.sort_by_key(|pair| pair.key.clone());

    let pos_idents: Vec<_> = (0..len)
        .map(|i| Ident::new(&format!("i{}", i), Span::call_site()))
        .collect();
    let arr_idents = quote! { [#(#pos_idents),*] };

    let mut arms = Vec::new();
    for &Pair { ref key, value } in &pairs {
        let arm = quote! { [#(#key),*] => #value, };
        arms.push(arm);
    }

    quote! {
        {
            let #arr_idents = #key else { unsafe { std::hint::unreachable_unchecked() } };

            match #arr_idents {
                #(#arms)*
                _ => return None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_generate_expr() {
        use super::*;

        let pairs = vec![
            Pair {
                key: b"abc".to_vec(),
                value: 13,
            },
            Pair {
                key: b"ab".to_vec(),
                value: 83,
            },
            Pair {
                key: b"a".to_vec(),
                value: 53,
            },
        ];

        let key = Ident::new("from_str", Span::call_site());
        let expr = generate_fn(pairs, &key);
        println!("{}", expr);
        panic!()
    }
}
