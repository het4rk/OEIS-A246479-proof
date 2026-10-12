# Proof of the conjectured column recurrences for OEIS A246479

[![Lean build](https://github.com/het4rk/OEIS-A246479-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A246479-proof/actions/workflows/lean.yml)

**Author:** Hetark Shah, AI-assisted by Grok  
**Date:** October 12, 2026

## Result

Let `T(n,k)` be the number of length `n+3` arrays over `0..k` with no pair in any four consecutive terms summing to exactly `k` ([A246479](https://oeis.org/A246479), R. H. Hardin, 2014). We prove, for all `n ≥ 0` (over ℤ):

- **every odd `k`:** `T(n+4) = (k−2)T(n+3) + 2T(n+2) + (k−2)T(n+1) + T(n)`
- **every even `k`:** `T(n+10) = (k−3)T(n+9) + 2T(n+8) + (k−3)T(n+7) + (k³−6k²+15k−13)T(n+6) + (3k²−11k+13)T(n+5) + (k³−7k²+19k−19)T(n+4) + (k²−4k+6)T(n+3) + T(n+2) + (k−2)T(n+1) + T(n)`

These are **Robert Israel's 2024 conjectures** in the entry (stated there for odd `k ≥ 5` and even `k ≥ 6`). We also prove all of Hardin's "Empirical for column k" formulas for `k = 1..9` verbatim, and **Colin Barker's conjectured closed forms** for rows 1–3 (A246480, A246481, A246482).

The method is a transfer-matrix argument on eleven types of triples, uniform in `k`. It extends the four-type argument from our A245995 proof. The naive transfer matrix has Θ(k³) states, so the new step is the reduction to eleven types. What this repo adds is that reduction, the proofs of Israel's and Barker's conjectures, and a machine-checked proof. No published proof was found (OEIS and web search, October 12, 2026).

## Status

**Complete proof** of Israel's two conjectures, Hardin's nine column formulas and Barker's row-1–3 formulas. Machine-checked. Hardin's row recurrences for `n ≥ 4` and the minimality of the recurrences are not covered (see the paper's Limitations section).

## Theorems and Lean names

| Lean name | Statement |
|---|---|
| `good_cons`, `N_succ` | prepending a letter (one-step recursion) |
| `typ`, `pair_sum`, `typ_step`, `N_eq_typ` | counts depend only on the triple type (11 types) |
| `T_eq_F` | `T` in terms of the type values |
| `T_odd_int`, `T_even_int`, `T_odd` | the general recurrences |
| `israel_odd`, `israel_even` | Israel's conjectures, verbatim in OEIS indexing |
| `T_col1` … `T_col9` | Hardin's formulas verbatim, e.g. `10 ≤ n → T n 4 = 2T(n−1) + T(n−3) + 14T(n−4) + 3T(n−5) + 6T(n−6) + T(n−8) + T(n−9)` |
| `row1_even` … `row3_odd` | Barker's closed forms for A246480–A246482 |

No `sorry` and no `native_decide`. `Values.lean` checks a few table values by kernel evaluation, and `scripts/check_bfile.py` checks the recursion against all 9999 terms of Hardin's b-file.

## Build

Toolchain `leanprover/lean4:v4.35.0-rc4`; Mathlib `v4.35.0-rc4` (pinned in `lake-manifest.json`).

```bash
cd A246479
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Axioms output

All 21 theorems in `Axioms.lean` report `[propext, Classical.choice, Quot.sound]` (see `verification/axioms.txt`).

## Machine-check attestation

- [`verification/`](verification/): `build-log.txt`, `axioms.txt`, and [`VERIFICATION.md`](verification/VERIFICATION.md) (toolchain, Mathlib commit, reproduce steps, SHA-256 of sources).
- [CI](https://github.com/het4rk/OEIS-A246479-proof/actions/workflows/lean.yml) does a clean build on every push, fails on any `sorry`, checks the axiom whitelist (`scripts/check_axioms.sh`), and uploads the `lean-attestation` artifact.

## Paper

[`paper/main.tex`](paper/main.tex) and [`paper/paper.pdf`](paper/paper.pdf).

## Citation

See [`CITATION.cff`](CITATION.cff):

> Hetark Shah (AI-assisted by Grok), *A proof of the conjectured column recurrences for OEIS A246479*, 2026. https://github.com/het4rk/OEIS-A246479-proof

## License

Apache-2.0 (the same as Mathlib). See [`LICENSE`](LICENSE).
