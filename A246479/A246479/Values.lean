import A246479.Rows

/-!
# Sanity checks

Values of `T` checked by kernel evaluation (`decide +kernel`, no extra axioms) against the
OEIS data, confirming the transcription of the definition and its indexing.
-/
namespace A246479
example : T 1 1 = 2 := by decide +kernel
example : T 1 2 = 10 := by decide +kernel
example : T 2 2 = 14 := by decide +kernel
example : T 1 3 = 60 := by decide +kernel
end A246479
