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
            #expr
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
        let expr = generate_arm_for_len(branch_pairs, key, len);
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

fn generate_arm_for_len(mut pairs: Vec<Pair>, key: &Ident, len: usize) -> TokenStream {
    pairs.sort_by_key(|pair| pair.key.clone());

    let pos_idents: Vec<_> = (0..len)
        .map(|i| Ident::new(&format!("i{}", i), Span::call_site()))
        .collect();

    let unique_cmps = generate_unique_cmps(&pairs, len, &pos_idents);
    let test_idxs: Vec<usize> = (0..len).filter(|&i| !is_unique_at(&pairs, i)).collect();

    let expr = generate_test_branch(&pairs, len, &pos_idents, &test_idxs, &unique_cmps);

    quote! {
        {
            let &[#(#pos_idents),*] = #key else { unsafe { std::hint::unreachable_unchecked() } };

            #expr

            None
        }
    }
}

fn generate_test_branch(
    pairs: &[Pair],
    len: usize,
    pos_idents: &[Ident],
    rem_test_idxs: &[usize],
    unique_cmps: &[TokenStream],
) -> TokenStream {
    assert!(!pairs.is_empty());

    if rem_test_idxs.is_empty() {
        let v = pairs[0].value;
        let cmp = unique_cmps[0].clone();

        if pairs.len() == 1 {
            return quote! {
                if #cmp {
                    return Some(#v);
                }
            };
        }

        let res = generate_test_branch(&pairs[1..], len, pos_idents, &[], unique_cmps);

        return quote! {
            if #cmp {
                return Some(#v);
            }

            #res
        };
    }

    let freq_of_test_at = |idx: usize| {
        let mut freqs = BTreeMap::new();
        for pair in pairs {
            let byte = pair.key[idx];
            *freqs.entry(byte).or_insert(0) += 1;
        }

        let (b, freq) = freqs
            .iter()
            .max_by_key(|&(_, &v)| v)
            .expect("no max freq found");
        (*b, *freq)
    };

    let (idx, (b, f)) = rem_test_idxs
        .iter()
        .map(|&idx| (idx, freq_of_test_at(idx)))
        .max_by_key(|&(_, (_, f))| f)
        .expect("no best idx found");

    let test_ident = &pos_idents[idx];
    let next_rem = rem_test_idxs
        .iter()
        .filter(|&&i| i != idx)
        .cloned()
        .collect::<Vec<_>>();

    let next_pairs_pos: Vec<_> = pairs
        .iter()
        .filter(|pair| pair.key[idx] == b)
        .cloned()
        .collect();

    let next_pairs_neg: Vec<_> = pairs
        .iter()
        .filter(|pair| pair.key[idx] != b)
        .cloned()
        .collect();

    let pos_br = || generate_test_branch(&next_pairs_pos, len, pos_idents, &next_rem, unique_cmps);

    let neg_br = || generate_test_branch(&next_pairs_neg, len, pos_idents, &next_rem, unique_cmps);

    if next_pairs_pos.is_empty() {
        let neg_br = neg_br();

        return quote! {
            if #test_ident != #b {
                #neg_br
            }
        };
    }

    if next_pairs_neg.is_empty() {
        let pos_br = pos_br();

        return quote! {
            if #test_ident == #b {
                #pos_br
            }
        };
    }

    assert!(!(next_pairs_neg.is_empty() || next_pairs_pos.is_empty()));

    let pos_br = pos_br();
    let neg_br = neg_br();
    quote! {
        if #test_ident == #b {
            #pos_br
        } else {
            #neg_br
        }
    }
}

fn generate_unique_cmps(pairs: &[Pair], len: usize, pos_idents: &[Ident]) -> Vec<TokenStream> {
    let uniques_idxs: Vec<usize> = (0..len).filter(|&i| is_unique_at(&pairs, i)).collect();
    let unique_pos_idents: Vec<_> = uniques_idxs
        .iter()
        .map(|&i| pos_idents[i].clone())
        .collect();

    let mut cmps = Vec::new();

    for pair in pairs {
        let unique_key: Vec<_> = uniques_idxs.iter().map(|&i| pair.key[i]).collect();

        let unique_conds = unique_pos_idents
            .iter()
            .zip(unique_key.iter())
            .map(|(pos, &byte)| {
                quote! { #pos == #byte }
            });

        let cmp = quote! {#(#unique_conds)&&*};
        cmps.push(cmp);
    }

    cmps
}

fn is_unique_at(pairs: &[Pair], idx: usize) -> bool {
    for x in pairs {
        for y in pairs {
            if x.key[idx] == y.key[idx] && x.key != y.key {
                return false;
            }
        }
    }

    true
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
