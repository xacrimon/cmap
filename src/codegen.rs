use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use std::collections::BTreeMap;
use syn::Expr;

#[derive(Clone)]
pub struct Pair {
    pub key: Vec<u8>,
    pub value: Expr,
}

pub fn generate_fn(pairs: Vec<Pair>, fn_name: &Ident, ty: &syn::Type) -> TokenStream {
    let key = Ident::new("bytes", Span::call_site());
    let expr = generate_expr(pairs, &key);

    quote! {
        const fn #fn_name(#key: &[u8]) -> Option<#ty> {
            use typenum::*;
            use std::ops::{Sub,Add,Shr,Mul};
            use typenum::uint::*;

            trait Counter {
                type Next: Counter;
                const COUNT: usize;
            }

            struct CounterImpl<Field> where Field:Unsigned {
                _field: std::marker::PhantomData<Field>,
            }

            impl Counter for CounterImpl<U0> {
                type Next = CounterImpl<U0>;
                const COUNT: usize = 0;
            }

            impl<Field> Counter for CounterImpl<UInt<Field, B1>>
            where
                UInt<Field, B1>: Unsigned + Shr<U1>,
                <UInt<Field, B1> as Shr<U1>>::Output: Unsigned + Shr<U1>,
                CounterImpl<<UInt<Field, B1> as Shr<U1>>::Output>: Counter,

            {
                type Next = CounterImpl<<UInt<Field, B1> as Shr<U1>>::Output>;
                const COUNT: usize = const { <UInt<Field, B1> as Unsigned>::USIZE.count_ones() as usize };
            }

            trait AsCounter {
                type Counter: Counter;
            }

            struct FieldMap<const N: usize>(std::marker::PhantomData<[(); N]>);

            impl<const N: usize> AsCounter for FieldMap<N>
            where
                Const<N> : ToUInt,
                <Const<N> as ToUInt>::Output: Unsigned,
                CounterImpl<U<N>>: Counter,
            {

                type Counter = CounterImpl<U<N>>;
            }

            #[inline(always)]
            const fn cmp_wrapper<const N:usize, const R:usize>(a: &[u8], b: &[u8]) -> bool
                where FieldMap<N>: AsCounter
            {
                cmp::<<FieldMap<N> as AsCounter>::Counter, N, R>(a.as_ptr(), b.as_ptr())
            }

            #[inline(always)]
            const fn cmp<C, const END: usize, const R:usize>(a: *const u8, b: *const u8) -> bool
            where
                C: Counter,
            {
                #[inline(always)]
                const fn adv(x: *const u8) -> *const u8 {
                    unsafe { x.add(8) }
                }

                macro_rules! load {
                    (u64, $ptr:expr) => {
                        unsafe { std::ptr::read_unaligned($ptr as *const u64) }
                    };
                    (u32, $ptr:expr) => {
                        unsafe { std::ptr::read_unaligned($ptr as *const u32) }
                    };
                    (u16, $ptr:expr) => {
                        unsafe { std::ptr::read_unaligned($ptr as *const u16) }
                    };
                    (u8, $ptr:expr) => {
                        unsafe { std::ptr::read_unaligned($ptr as *const u8) }
                    };
                }

                if const { C::COUNT > 0 } {
                    let b0 = load!(u64, a) == load!(u64, b);
                    let b1 = cmp::<C::Next, END, R>(adv(a),adv(b));
                    b0 && b1
                } else if const { R == 0 } {
                    true
                } else if const { R == 1 } {
                    load!(u8, a) == load!(u8, b)
                } else if const { R == 2 } {
                    load!(u16, a) == load!(u16, b)
                } else if const { R == 3 } {
                    load!(u16, a) == load!(u16, b) && load!(u8, a.add(2)) == load!(u8, b.add(2))
                } else if const { R == 4 } {
                    load!(u32, a) == load!(u32, b)
                } else if const { R == 5 } {
                    load!(u32, a) == load!(u32, b) && load!(u8, a.add(4)) == load!(u8, b.add(4))
                } else if const { R == 6 } {
                    load!(u32, a) == load!(u32, b) && load!(u16, a.add(4)) == load!(u16, b.add(4))
                } else if const { R == 7 } {
                    load!(u32, a) == load!(u32, b) && load!(u16, a.add(4)) == load!(u16, b.add(4))
                        && load!(u8, a.add(6)) == load!(u8, b.add(6))
                } else {
                    unsafe { std::hint::unreachable_unchecked(); }
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

        let cmp_len = hi - lo + 1;
        let steps = cmp_len / 8;
        let n = 2usize.pow(steps as u32) - 1;
        let rem = cmp_len % 8;

        let test_subsl =
            quote! { unsafe { std::slice::from_raw_parts(bytes.as_ptr().add(#lo), #cmp_len) } };
        let cmp = quote! { cmp_wrapper::<#n, #rem>(#test_subsl, #lit_subsl) };
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
