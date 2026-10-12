import A246479.Forms

/-!
# Column recurrences for OEIS A246479

* `T_odd_int`  : every odd `k`  — Robert Israel's conjectured order-4 recurrence.
* `T_even_int` : every even `k` — Robert Israel's conjectured order-10 recurrence.
* `T_col1` … `T_col9` : R. H. Hardin's empirical column formulas (OEIS indexing,
  `a(n) = T(n,k)`), verbatim.
* `israel_odd`, `israel_even` : Israel's statements verbatim in OEIS indexing.
-/

set_option linter.unusedSimpArgs false

namespace A246479

lemma V_add (k n : ℕ) : ∀ i, V k (n + i + 1) = step k (V k (n + i)) := fun _ => rfl

/-- Odd `k`: `T(n+4) = (k-2) T(n+3) + 2 T(n+2) + (k-2) T(n+1) + T(n)` (over `ℤ`). -/
theorem T_odd_int {k : ℕ} (hk : Odd k) (n : ℕ) :
    (T (n + 4) k : ℤ) = ((k : ℤ) - 2) * T (n + 3) k + 2 * T (n + 2) k
      + ((k : ℤ) - 2) * T (n + 1) k + T n k := by
  have he := eps_odd hk
  simp only [T_eq_F, V_succ, Go_base he, Go_chain0 he, Go_chain1 he, Go_chain2 he,
    Go_chain3 he]
  unfold Go0 Go1 Go2 Go3 Go4; ring

/-- Even `k`: Israel's order-10 recurrence (over `ℤ`). -/
theorem T_even_int {k : ℕ} (hk : Even k) (n : ℕ) :
    (T (n + 10) k : ℤ) = ((k : ℤ) - 3) * T (n + 9) k + 2 * T (n + 8) k
      + ((k : ℤ) - 3) * T (n + 7) k
      + ((k : ℤ) ^ 3 - 6 * k ^ 2 + 15 * k - 13) * T (n + 6) k
      + (3 * (k : ℤ) ^ 2 - 11 * k + 13) * T (n + 5) k
      + ((k : ℤ) ^ 3 - 7 * k ^ 2 + 19 * k - 19) * T (n + 4) k
      + ((k : ℤ) ^ 2 - 4 * k + 6) * T (n + 3) k + T (n + 2) k
      + ((k : ℤ) - 2) * T (n + 1) k + T n k := by
  have he := eps_even hk
  simp only [T_eq_F, V_succ, Ge_base he, Ge_chain0 he, Ge_chain1 he, Ge_chain2 he,
    Ge_chain3 he, Ge_chain4 he, Ge_chain5 he, Ge_chain6 he, Ge_chain7 he, Ge_chain8 he,
    Ge_chain9 he]
  unfold Ge0 Ge1 Ge2 Ge3 Ge4 Ge5 Ge6 Ge7 Ge8 Ge9 Ge10; ring

/-- Odd `k ≥ 3`, over `ℕ`. -/
theorem T_odd {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) (n : ℕ) :
    T (n + 4) k = (k - 2) * T (n + 3) k + 2 * T (n + 2) k + (k - 2) * T (n + 1) k + T n k := by
  have h := T_odd_int hk n
  have : 2 ≤ k := by omega
  zify [this]; exact h

/-- Robert Israel's conjecture for odd `k ≥ 5`, verbatim in OEIS indexing (`n ≥ 5`). -/
theorem israel_odd {k : ℕ} (hk : Odd k) (hk5 : 5 ≤ k) (n : ℕ) (hn : 5 ≤ n) :
    T n k = (k - 2) * T (n - 1) k + 2 * T (n - 2) k + (k - 2) * T (n - 3) k + T (n - 4) k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simpa using T_odd hk (by omega) m

/-- Robert Israel's conjecture for even `k ≥ 6`, verbatim in OEIS indexing (`n ≥ 11`),
read over `ℤ` (the coefficient `k^3 - 7k^2 + 19k - 19` is an integer polynomial). -/
theorem israel_even {k : ℕ} (hk : Even k) (n : ℕ) (hn : 11 ≤ n) :
    (T n k : ℤ) = ((k : ℤ) - 3) * T (n - 1) k + 2 * T (n - 2) k + ((k : ℤ) - 3) * T (n - 3) k
      + ((k : ℤ) ^ 3 - 6 * k ^ 2 + 15 * k - 13) * T (n - 4) k
      + (3 * (k : ℤ) ^ 2 - 11 * k + 13) * T (n - 5) k
      + ((k : ℤ) ^ 3 - 7 * k ^ 2 + 19 * k - 19) * T (n - 6) k
      + ((k : ℤ) ^ 2 - 4 * k + 6) * T (n - 7) k + T (n - 8) k
      + ((k : ℤ) - 2) * T (n - 9) k + T (n - 10) k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  simpa using T_even_int hk m

/-! ## Hardin's column formulas, verbatim (OEIS indexing, `a(n) = T(n,k)`). -/

theorem T_col1 (n : ℕ) (hn : 2 ≤ n) : T n 1 = T (n - 1) 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have he := eps_odd (k := 1) (by decide)
  have h : (T (m + 1) 1 : ℤ) = T m 1 := by
    simp only [T_eq_F, V_succ, G1__base he, G1__chain0 he]
    simp only [G1_0, G1_1]
  simpa using h

theorem T_col2 (n : ℕ) (hn : 5 ≤ n) : T n 2 = T (n - 1) 2 + T (n - 4) 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have he := eps_even (k := 2) (by decide)
  have h : (T (m + 4) 2 : ℤ) = T (m + 3) 2 + T m 2 := by
    simp only [T_eq_F, V_succ, G2__base he, G2__chain0 he, G2__chain1 he, G2__chain2 he,
      G2__chain3 he]
    simp only [G2_0, G2_1, G2_2, G2_3, G2_4]; ring
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 4 = m by omega]
  exact_mod_cast h

theorem T_col3 (n : ℕ) (hn : 4 ≤ n) : T n 3 = 2 * T (n - 1) 3 + T (n - 3) 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have he := eps_odd (k := 3) (by decide)
  have h : (T (m + 3) 3 : ℤ) = 2 * T (m + 2) 3 + T m 3 := by
    simp only [T_eq_F, V_succ, G3__base he, G3__chain0 he, G3__chain1 he, G3__chain2 he]
    simp only [G3_0, G3_1, G3_2, G3_3]; ring
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 3 = m by omega]
  exact_mod_cast h

theorem T_col4 (n : ℕ) (hn : 10 ≤ n) :
    T n 4 = 2 * T (n - 1) 4 + T (n - 3) 4 + 14 * T (n - 4) 4 + 3 * T (n - 5) 4
      + 6 * T (n - 6) 4 + T (n - 8) 4 + T (n - 9) 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  have he := eps_even (k := 4) (by decide)
  have h : (T (m + 9) 4 : ℤ) = 2 * T (m + 8) 4 + T (m + 6) 4 + 14 * T (m + 5) 4
      + 3 * T (m + 4) 4 + 6 * T (m + 3) 4 + T (m + 1) 4 + T m 4 := by
    simp only [T_eq_F, V_succ, G4__base he, G4__chain0 he, G4__chain1 he, G4__chain2 he,
      G4__chain3 he, G4__chain4 he, G4__chain5 he, G4__chain6 he, G4__chain7 he, G4__chain8 he]
    simp only [G4_0, G4_1, G4_2, G4_3, G4_4, G4_5, G4_6, G4_7, G4_8, G4_9]; ring
  have e : m + 9 - 1 = m + 8 ∧ m + 9 - 3 = m + 6 ∧ m + 9 - 4 = m + 5 ∧ m + 9 - 5 = m + 4 ∧
      m + 9 - 6 = m + 3 ∧ m + 9 - 8 = m + 1 ∧ m + 9 - 9 = m := by omega
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1, e.2.2.2.2.2.1, e.2.2.2.2.2.2]
  exact_mod_cast h

theorem T_col5 (n : ℕ) (hn : 5 ≤ n) :
    T n 5 = 3 * T (n - 1) 5 + 2 * T (n - 2) 5 + 3 * T (n - 3) 5 + T (n - 4) 5 :=
  israel_odd (k := 5) (by decide) le_rfl n hn

theorem T_col6 (n : ℕ) (hn : 11 ≤ n) :
    T n 6 = 3 * T (n - 1) 6 + 2 * T (n - 2) 6 + 3 * T (n - 3) 6 + 77 * T (n - 4) 6
      + 55 * T (n - 5) 6 + 59 * T (n - 6) 6 + 18 * T (n - 7) 6 + T (n - 8) 6
      + 4 * T (n - 9) 6 + T (n - 10) 6 := by
  have h := israel_even (k := 6) (by decide) n hn
  norm_num at h
  exact_mod_cast h

theorem T_col7 (n : ℕ) (hn : 5 ≤ n) :
    T n 7 = 5 * T (n - 1) 7 + 2 * T (n - 2) 7 + 5 * T (n - 3) 7 + T (n - 4) 7 :=
  israel_odd (k := 7) (by decide) (by norm_num) n hn

theorem T_col8 (n : ℕ) (hn : 11 ≤ n) :
    T n 8 = 5 * T (n - 1) 8 + 2 * T (n - 2) 8 + 5 * T (n - 3) 8 + 235 * T (n - 4) 8
      + 117 * T (n - 5) 8 + 197 * T (n - 6) 8 + 38 * T (n - 7) 8 + T (n - 8) 8
      + 6 * T (n - 9) 8 + T (n - 10) 8 := by
  have h := israel_even (k := 8) (by decide) n hn
  norm_num at h
  exact_mod_cast h

theorem T_col9 (n : ℕ) (hn : 5 ≤ n) :
    T n 9 = 7 * T (n - 1) 9 + 2 * T (n - 2) 9 + 7 * T (n - 3) 9 + T (n - 4) 9 :=
  israel_odd (k := 9) (by decide) (by norm_num) n hn

end A246479
