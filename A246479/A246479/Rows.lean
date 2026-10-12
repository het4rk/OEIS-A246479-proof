import A246479.Main

/-!
# Rows 1–3 of A246479 (OEIS A246480, A246481, A246482)

Colin Barker's conjectured closed forms (Nov 06 2018), in terms of `k`
(the OEIS index of these row sequences).
-/

namespace A246479

private lemma V1 (k : ℕ) : V k 1 = step k ones := rfl
private lemma V2 (k : ℕ) : V k 2 = step k (step k ones) := rfl
private lemma V3 (k : ℕ) : V k 3 = step k (step k (step k ones)) := rfl

/-- A246480, `k` even. -/
theorem row1_even {k : ℕ} (hk : Even k) :
    (T 1 k : ℤ) = (k : ℤ) ^ 4 - 2 * k ^ 3 + 3 * k ^ 2 - k := by
  have he := eps_even hk
  simp only [T_eq_F, V1, Ge_base he, Ge_chain0 he]
  simp only [Ge1, ones]; ring

/-- A246480, `k` odd. -/
theorem row1_odd {k : ℕ} (hk : Odd k) :
    (T 1 k : ℤ) = (k : ℤ) ^ 4 - 2 * k ^ 3 + 3 * k ^ 2 + 3 * k - 3 := by
  have he := eps_odd hk
  simp only [T_eq_F, V1, Go_base he, Go_chain0 he]
  simp only [Go1, ones]; ring

/-- A246481, `k` even. -/
theorem row2_even {k : ℕ} (hk : Even k) :
    (T 2 k : ℤ) = (k : ℤ) ^ 5 - 4 * k ^ 4 + 10 * k ^ 3 - 11 * k ^ 2 + 5 * k := by
  have he := eps_even hk
  simp only [T_eq_F, V2, Ge_base he, Ge_chain0 he, Ge_chain1 he]
  simp only [Ge2, ones]; ring

/-- A246481, `k` odd. -/
theorem row2_odd {k : ℕ} (hk : Odd k) :
    (T 2 k : ℤ) = (k : ℤ) ^ 5 - 4 * k ^ 4 + 10 * k ^ 3 - 4 * k ^ 2 - 10 * k + 9 := by
  have he := eps_odd hk
  simp only [T_eq_F, V2, Go_base he, Go_chain0 he, Go_chain1 he]
  simp only [Go2, ones]; ring

/-- A246482, `k` even. -/
theorem row3_even {k : ℕ} (hk : Even k) :
    (T 3 k : ℤ) = (k : ℤ) ^ 6 - 6 * k ^ 5 + 21 * k ^ 4 - 40 * k ^ 3 + 43 * k ^ 2 - 20 * k := by
  have he := eps_even hk
  simp only [T_eq_F, V3, Ge_base he, Ge_chain0 he, Ge_chain1 he, Ge_chain2 he]
  simp only [Ge3, ones]; ring

/-- A246482, `k` odd. -/
theorem row3_odd {k : ℕ} (hk : Odd k) :
    (T 3 k : ℤ) = (k : ℤ) ^ 6 - 6 * k ^ 5 + 21 * k ^ 4 - 30 * k ^ 3 + 5 * k ^ 2 + 37 * k - 26 := by
  have he := eps_odd hk
  simp only [T_eq_F, V3, Go_base he, Go_chain0 he, Go_chain1 he, Go_chain2 he]
  simp only [Go3, ones]; ring

end A246479
