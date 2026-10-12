# Verification record

| Item | Value |
|---|---|
| Date | 2026-10-12 |
| Verified commit | `4aa3998c123c4fcb5674c801d2f25c9c19203466` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4` |
| Mathlib | `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Build result | `Build completed successfully` (see [`build-log.txt`](build-log.txt)) |
| Axioms | 21 declarations, all `[propext, Classical.choice, Quot.sound]` (see [`axioms.txt`](axioms.txt)) |
| CI | [![Lean build](https://github.com/het4rk/OEIS-A246479-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/OEIS-A246479-proof/actions/workflows/lean.yml) |

## Reproduce

```bash
git clone https://github.com/het4rk/OEIS-A246479-proof
cd OEIS-A246479-proof
git checkout 4aa3998c123c4fcb5674c801d2f25c9c19203466
cd A246479
lake exe cache get
lake build
lake env lean Axioms.lean
grep -rnw sorry A246479 --include=*.lean   # expect no output
```

## No-sorry check

`grep -rnw sorry A246479/A246479 --include=*.lean` gave no matches, and the build log has no `declaration uses 'sorry'` warnings. No `native_decide` is used.

Fresh clone of that commit: `lake exe cache get`, `lake build` (success), `lake env lean Axioms.lean` checked by `scripts/check_axioms.sh` (OK, 21 declarations).

## b-file check

`scripts/check_bfile.py` reproduces all 9999 terms of Hardin's b-file (b246479.txt) from the type recursion.

## SHA-256 of the Lean sources (at the verified commit)

```
8780650528db4190484e167ed5d8f9b367075606372d2739af04f21bb9f653b3  A246479.lean
148d5473d8385ffa1e457942a110d106c31982dcd01f95f11a26c47dcbe5d9f0  Axioms.lean
016157fa18256d41db92477584e96728071635dc56e3ca1c0e69ecd8ee0b1ea3  A246479/Basic.lean
4bc4195074a291b4f757971a2795f2aa03c8bf5cc34189835b0cb6cf6b1cabe8  A246479/Forms.lean
dc14977914eeb023491a4cf12106d3b66445c5defd48f8048017752167202f31  A246479/Main.lean
96c315050d411871a92c88468243aa97b849aba45702d1068c335a0d82c27c45  A246479/Rows.lean
83fc839915bc01704416b276281909bc37e8941ef229bbe12be00d751a5d3a0b  A246479/Step.lean
07d13ecfd7c48a84c84d06ee209aaba389ae408e8fbc781e78804bbbfc812167  A246479/Types.lean
01ab690755ba4e1ed7730f2c316cdeaae032b7f3da1a326749f91942023553fb  A246479/Values.lean
2eef5bfb52a87c9bd0d801ff664fe2efc6304a10b108208c307a1afbbec0d90c  lakefile.toml
906875f080a7a7ef71af416a26e8d89531ded61107fe4523e06a89b8078e933c  lake-manifest.json
8f89aa44fccdb1a0b6cc768c7c9f54b94cd40e47a08d582f82d1235f13075cf7  lean-toolchain
```
