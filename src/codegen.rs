use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use syn::Expr;
use std::collections::BTreeMap;

#[derive(Clone)]
pub struct Pair {
    pub key: Vec<u8>,
    pub value: Expr,
}

use typenum::*;
use std::ops::{Shl,Sub,Add};

trait Counter<Field> where Field:Unsigned {
    type Next: Counter<Field>;
}

struct CounterImpl<Field> where Field:Unsigned {
    _field: std::marker::PhantomData<Field>,
}

//impl Counter<U0> for CounterImpl<U0>
//
//{
//    type Next = CounterImpl<U0>;
//}

impl<Field> Counter<Field> for CounterImpl<Field>
where
    Field: Unsigned + Sub<U1> + NonZero,
    <Field as Sub<U1>>::Output: Unsigned + Sub<U1>,
    CounterImpl<<Field as Sub<U1>>::Output>: Counter<Field>,
    //<Field as Shl<U1>::Output>: Unsigned + Shl<U1>,
    //<<Field as Shl<U1>::Output> as Shl<U1>>::Output: Unsigned + Shl<U1>,

{
    type Next = CounterImpl<<Field as Sub<U1>>::Output>;
}

//impl<Field> Counter<Field> for CounterImpl<Field>
//where
//    Field: Unsigned + Shl<U1>,
//    <Field as Shl<U1>>::Output: Unsigned + Shl<U1>,
//    CounterImpl<<Field as Shl<U1>>::Output>: Counter<Field>,
//{
//    type Next = CounterImpl<<Field as Shl<U1>>::Output>;
//}

pub fn generate_fn(pairs: Vec<Pair>, fn_name: &Ident, ty: &syn::Type) -> TokenStream {
    let key = Ident::new("bytes", Span::call_site());
    let expr = generate_expr(pairs, &key);

    quote! {
        const fn #fn_name(#key: &[u8]) -> Option<#ty> {
            use typenum::*;
            use std::ops::{Shl,Sub,Add};

            trait Counter<Field> where Field:Unsigned {
                type Next: Counter<Field>;
            }
            
            struct CounterImpl<Field> where Field:Unsigned {
                _field: std::marker::PhantomData<Field>,
            }

            impl Counter<U0> for CounterImpl<U0> {
                type Next = CounterImpl<U0>;
            }

            impl<Field> Counter<Field> for CounterImpl<Field>
            where
                Field: Unsigned + Sub<U1>,
                <Field as Sub<U1>>::Output: Unsigned + Sub<U1>,
                CounterImpl<<Field as Sub<U1>>::Output>: Counter<Field>,

            {
                type Next = CounterImpl<<Field as Sub<U1>>::Output>;
            }

            const fn cmp_wrapper<const N:usize>(a: &[u8], b: &[u8]) -> bool {
                cmp::<CounterImpl<U0>, U0, N>(a, b)
            }

            const fn cmp<C, F, const END: usize>(a: &[u8], b: &[u8]) -> bool
            where
                C: Counter<F>,
                F: Unsigned,
            {
                const fn adv(a: &[u8]) -> &[u8] {
                    let a = unsafe { std::slice::from_raw_parts(a.as_ptr().add(8), a.len() - 8) };
                    a
                }

                let a = unsafe { a.first_chunk::<8>().unwrap_unchecked() };
                let b = unsafe { b.first_chunk::<8>().unwrap_unchecked() };

                if const { F::USIZE == 0} {
                    let b0 = u64::from_ne_bytes([a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]]) == u64::from_ne_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]);
                    //let b1 = cmp::<C::Next, _, END>(adv(a), adv(b));
                }

                //if const { <<N as STEPPED>::CONTINUE as Bit>::BOOL } {
                //    let a = unsafe { a.first_chunk::<8>().unwrap_unchecked() };
                //    let b = unsafe { b.first_chunk::<8>().unwrap_unchecked() };
                //    let b0 = u64::from_ne_bytes([a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]]) == u64::from_ne_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]);
                //    return b0 && cmp::<N::CHILD>(adv(a), adv(b));
                //}

                false
            }

            #[inline(always)]
            const fn bs_eq<const N:usize>(a: &[u8], b: &[u8]) -> bool where Const<N>: ToUInt {
                let a = unsafe { a.first_chunk::<N>().unwrap_unchecked() };
                let b = unsafe { b.first_chunk::<N>().unwrap_unchecked() };

                const fn adv(a: &[u8]) -> &[u8] {
                    let a = unsafe { std::slice::from_raw_parts(a.as_ptr().add(8), a.len() - 8) };
                    a
                }

                if const { N == 0 } {
                    true
                } else if const { N == 1 } {
                    a[0] == b[0]
                } else if const { N == 2 } {
                    u16::from_ne_bytes([a[0], a[1]]) == u16::from_ne_bytes([b[0], b[1]])
                } else if const { N == 3 } {
                    u16::from_ne_bytes([a[0], a[1]]) == u16::from_ne_bytes([b[0], b[1]])
                        && a[2] == b[2]
                } else if const { N == 4 } {
                    u32::from_ne_bytes([a[0], a[1], a[2], a[3]]) == u32::from_ne_bytes([b[0], b[1], b[2], b[3]])
                } else if const { N == 5 } {
                    u32::from_ne_bytes([a[0], a[1], a[2], a[3]]) == u32::from_ne_bytes([b[0], b[1], b[2], b[3]])
                        && a[4] == b[4]
                } else if const { N == 6 } {
                    u32::from_ne_bytes([a[0], a[1], a[2], a[3]]) == u32::from_ne_bytes([b[0], b[1], b[2], b[3]])
                        && u16::from_ne_bytes([a[4], a[5]]) == u16::from_ne_bytes([b[4], b[5]])
                } else if const { N == 7 } {
                    u32::from_ne_bytes([a[0], a[1], a[2], a[3]]) == u32::from_ne_bytes([b[0], b[1], b[2], b[3]])
                        && u16::from_ne_bytes([a[4], a[5]]) == u16::from_ne_bytes([b[4], b[5]])
                        && a[6] == b[6]
                } else if const { N == 8 } {
                    u64::from_ne_bytes([a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]]) == u64::from_ne_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
                } else {
                    let mut i = 0;
                    while i < N {
                        if a[i] != b[i] {
                            return false;
                        }
                        i += 1;
                    }
                    true
                }
            }

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
        .map(|i| Ident::new(&format!("_i{}", i), Span::call_site()))
        .collect();

    let test_idxs: Vec<usize> = (0..len).filter(|&i| !is_unique_at(&pairs, i)).collect();
    let mut alr_tst = Vec::new();

    let expr = generate_test_branch(&pairs, len, &pos_idents, &test_idxs, &mut alr_tst);

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
    alr_tst: &mut Vec<usize>,
) -> TokenStream {
    assert!(!pairs.is_empty());

    if rem_test_idxs.is_empty() || pairs.len() == 1 {
        let pair = &pairs[0];
        let value = &pair.value;
        let uniques_idxs: Vec<usize> = (0..len)
            .filter(|&i| !alr_tst.contains(&i) && is_unique_at(&pairs, i))
            .collect();
        let cmp = generate_unique_cmp(pair, pos_idents, &uniques_idxs);

        if pairs.len() == 1 {
            return quote! {
                if #cmp {
                    return Some(#value);
                }
            };
        }

        let res = generate_test_branch(&pairs[1..], len, pos_idents, &[], alr_tst);

        return quote! {
            if #cmp {
                return Some(#value);
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

    let (idx, (b, _freq)) = rem_test_idxs
        .iter()
        .map(|&idx| (idx, freq_of_test_at(idx)))
        .max_by_key(|&(_, (_, f))| f)
        .expect("no best idx found");

    alr_tst.push(idx);

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

    macro_rules! pos_br {
        () => {
            generate_test_branch(&next_pairs_pos, len, pos_idents, &next_rem, alr_tst)
        };
    }

    macro_rules! neg_br {
        () => {
            generate_test_branch(&next_pairs_neg, len, pos_idents, &next_rem, alr_tst)
        };
    }

    if next_pairs_pos.is_empty() {
        let neg_br = neg_br!();

        return quote! {
            if #test_ident != #b {
                #neg_br
            }
        };
    }

    if next_pairs_neg.is_empty() {
        let pos_br = pos_br!();

        return quote! {
            if #test_ident == #b {
                #pos_br
            }
        };
    }

    assert!(!(next_pairs_neg.is_empty() || next_pairs_pos.is_empty()));

    let pos_br = pos_br!();
    let neg_br = neg_br!();
    quote! {
        if #test_ident == #b {
            #pos_br
        } else {
            #neg_br
        }
    }
}

fn generate_unique_cmp(pair: &Pair, pos_idents: &[Ident], unique_idxs: &[usize]) -> TokenStream {
    let mut idxs = unique_idxs.to_vec();
    idxs.sort();

    let mut conds = Vec::new();

    for contig in idxs.chunk_by(|i0, i1| i1 - i0 == 1) {
        if contig.len() == 1 {
            let idx = contig[0];
            let pos = &pos_idents[idx];
            let byte = pair.key[idx];
            let cmp = quote! { #pos == #byte };
            conds.push(cmp);
            continue;
        }

        let lo = contig[0];
        let hi = contig[contig.len() - 1];

        let lits = &pair.key[lo..=hi];
        let lit_subsl = quote! { &[#(#lits),*] };

        let cmp_len = hi-lo+1;

        let test_subsl = quote! { unsafe { std::slice::from_raw_parts(bytes.as_ptr().add(#lo), #cmp_len) } };
        let cmp = quote! { bs_eq::<#cmp_len>(#test_subsl, #lit_subsl) };
        conds.push(cmp);
    }

    quote! {#(#conds)&&*}
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
        let expr = generate_fn(pairs, &key, &syn::parse_str("i32").unwrap());
        println!("{}", expr);
        panic!()
    }
}
