import A246479.Step

/-!
# Column recurrences for OEIS A246479, proved

The linear forms `Go i`, `Ge i` are `F ∘ step^i` (odd and even `k`), written out explicitly so
that each chain step is a small `ring` identity.
-/

namespace A246479

lemma eps_eq_one (k : ℕ) {h : Fin (k + 1)} (hh : h.rev = h) : eps k = 1 := by
  unfold eps
  rw [Finset.card_eq_one]
  refine ⟨h, ?_⟩
  ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun ha => mid_unique ha hh, fun ha => ha ▸ hh⟩

lemma eps_odd {k : ℕ} (hk : Odd k) : eps k = 0 := by
  unfold eps
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ h
  rw [Fin.ext_iff, Fin.val_rev] at h
  obtain ⟨m, hm⟩ := hk
  have := a.isLt
  omega

lemma eps_even {k : ℕ} (hk : Even k) : eps k = 1 := by
  obtain ⟨m, hm⟩ := hk
  refine eps_eq_one k (h := ⟨m, by omega⟩) ?_
  rw [Fin.ext_iff, Fin.val_rev]; simp; omega

/-- `F ∘ step^0` as an explicit linear form -/
def Go0 (k : ℤ) (v : St) : ℤ :=
  (k + 1) * v.A +
    (k^2 - 1) * v.B +
    (k^2 - 1) * v.C +
    (k^2 - 1) * v.D +
    (k^3 - 3*k^2 - k + 3) * v.E

/-- `F ∘ step^1` as an explicit linear form -/
def Go1 (k : ℤ) (v : St) : ℤ :=
  (k^2 + k) * v.A +
    (k^3 - k^2 - k + 1) * v.B +
    (k^3 - k^2 - k + 1) * v.C +
    (k^3 - k^2 - k + 1) * v.D +
    (k^4 - 5*k^3 + 5*k^2 + 5*k - 6) * v.E

/-- `F ∘ step^2` as an explicit linear form -/
def Go2 (k : ℤ) (v : St) : ℤ :=
  (k^3 + 1) * v.A +
    (k^4 - 2*k^3 + k^2 + 2*k - 2) * v.B +
    (k^4 - 3*k^3 + 3*k^2 + 3*k - 4) * v.C +
    (k^4 - 3*k^3 + 3*k^2 + 3*k - 4) * v.D +
    (k^5 - 7*k^4 + 17*k^3 - 11*k^2 - 18*k + 18) * v.E

/-- `F ∘ step^3` as an explicit linear form -/
def Go3 (k : ℤ) (v : St) : ℤ :=
  (k^4 - 2*k^3 + 3*k^2 + 3*k - 3) * v.A +
    (k^5 - 4*k^4 + 8*k^3 - 3*k^2 - 9*k + 7) * v.B +
    (k^5 - 5*k^4 + 12*k^3 - 7*k^2 - 13*k + 12) * v.C +
    (k^5 - 5*k^4 + 12*k^3 - 7*k^2 - 13*k + 12) * v.D +
    (k^6 - 9*k^5 + 34*k^4 - 60*k^3 + 19*k^2 + 69*k - 54) * v.E

/-- `F ∘ step^4` as an explicit linear form -/
def Go4 (k : ℤ) (v : St) : ℤ :=
  (k^5 - 4*k^4 + 10*k^3 - 4*k^2 - 10*k + 9) * v.A +
    (k^6 - 6*k^5 + 19*k^4 - 26*k^3 + k^2 + 32*k - 21) * v.B +
    (k^6 - 7*k^5 + 25*k^4 - 40*k^3 + 9*k^2 + 47*k - 35) * v.C +
    (k^6 - 7*k^5 + 25*k^4 - 40*k^3 + 9*k^2 + 47*k - 35) * v.D +
    (k^7 - 11*k^6 + 55*k^5 - 149*k^4 + 189*k^3 + k^2 - 245*k + 159) * v.E

lemma Go_base {k : ℕ} (he : eps k = 0) (v : St) : F k v = Go0 (k : ℤ) v := by
  unfold F Rm Rx Sxx Snm Sxm Sym Go0; rw [he]; push_cast; ring

lemma Go_chain0 {k : ℕ} (he : eps k = 0) (v : St) :
    Go0 (k : ℤ) (step k v) = Go1 (k : ℤ) v := by
  unfold Go0 Go1 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Go_chain1 {k : ℕ} (he : eps k = 0) (v : St) :
    Go1 (k : ℤ) (step k v) = Go2 (k : ℤ) v := by
  unfold Go1 Go2 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Go_chain2 {k : ℕ} (he : eps k = 0) (v : St) :
    Go2 (k : ℤ) (step k v) = Go3 (k : ℤ) v := by
  unfold Go2 Go3 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Go_chain3 {k : ℕ} (he : eps k = 0) (v : St) :
    Go3 (k : ℤ) (step k v) = Go4 (k : ℤ) v := by
  unfold Go3 Go4 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

/-- `F ∘ step^0` as an explicit linear form -/
def Ge0 (k : ℤ) (v : St) : ℤ :=
  (k) * v.A +
    (k^2 - 2*k) * v.B +
    (k) * v.Bm +
    (k^2 - 2*k) * v.C +
    (k) * v.Cm +
    (k^2 - 2*k) * v.D +
    (k) * v.Dm +
    (k^3 - 6*k^2 + 8*k) * v.E +
    (k^2 - 2*k) * v.E1 +
    (k^2 - 2*k) * v.E2 +
    (k^2 - 2*k) * v.E3

/-- `F ∘ step^1` as an explicit linear form -/
def Ge1 (k : ℤ) (v : St) : ℤ :=
  (k^2) * v.A +
    (k^3 - 3*k^2 + 2*k) * v.B +
    (k^2 - k) * v.Bm +
    (k^3 - 3*k^2 + 2*k) * v.C +
    (k^2 - k) * v.Cm +
    (k^3 - 3*k^2 + 2*k) * v.D +
    (k^2 - k) * v.Dm +
    (k^4 - 8*k^3 + 20*k^2 - 16*k) * v.E +
    (k^3 - 4*k^2 + 4*k) * v.E1 +
    (k^3 - 4*k^2 + 4*k) * v.E2 +
    (k^3 - 4*k^2 + 4*k) * v.E3

/-- `F ∘ step^2` as an explicit linear form -/
def Ge2 (k : ℤ) (v : St) : ℤ :=
  (k^3 - k^2 + k) * v.A +
    (k^4 - 4*k^3 + 6*k^2 - 4*k) * v.B +
    (k^3 - 2*k^2 + 2*k) * v.Bm +
    (k^4 - 5*k^3 + 10*k^2 - 8*k) * v.C +
    (k^3 - 3*k^2 + 3*k) * v.Cm +
    (k^4 - 5*k^3 + 10*k^2 - 8*k) * v.D +
    (k^3 - 3*k^2 + 3*k) * v.Dm +
    (k^5 - 10*k^4 + 38*k^3 - 68*k^2 + 48*k) * v.E +
    (k^4 - 6*k^3 + 13*k^2 - 10*k) * v.E1 +
    (k^4 - 6*k^3 + 13*k^2 - 10*k) * v.E2 +
    (k^4 - 6*k^3 + 14*k^2 - 12*k) * v.E3

/-- `F ∘ step^3` as an explicit linear form -/
def Ge3 (k : ℤ) (v : St) : ℤ :=
  (k^4 - 3*k^3 + 6*k^2 - 4*k) * v.A +
    (k^5 - 6*k^4 + 17*k^3 - 26*k^2 + 16*k) * v.B +
    (k^4 - 4*k^3 + 9*k^2 - 7*k) * v.Bm +
    (k^5 - 7*k^4 + 23*k^3 - 39*k^2 + 26*k) * v.C +
    (k^4 - 5*k^3 + 12*k^2 - 10*k) * v.Cm +
    (k^5 - 7*k^4 + 23*k^3 - 39*k^2 + 26*k) * v.D +
    (k^4 - 5*k^3 + 10*k^2 - 7*k) * v.Dm +
    (k^6 - 12*k^5 + 61*k^4 - 169*k^3 + 250*k^2 - 152*k) * v.E +
    (k^5 - 8*k^4 + 26*k^3 - 40*k^2 + 24*k) * v.E1 +
    (k^5 - 8*k^4 + 28*k^3 - 48*k^2 + 32*k) * v.E2 +
    (k^5 - 8*k^4 + 29*k^3 - 52*k^2 + 36*k) * v.E3

/-- `F ∘ step^4` as an explicit linear form -/
def Ge4 (k : ℤ) (v : St) : ℤ :=
  (k^5 - 5*k^4 + 15*k^3 - 23*k^2 + 15*k) * v.A +
    (k^6 - 8*k^5 + 32*k^4 - 76*k^3 + 100*k^2 - 56*k) * v.B +
    (k^5 - 6*k^4 + 20*k^3 - 33*k^2 + 22*k) * v.Bm +
    (k^6 - 9*k^5 + 40*k^4 - 103*k^3 + 145*k^2 - 86*k) * v.C +
    (k^5 - 7*k^4 + 25*k^3 - 43*k^2 + 29*k) * v.Cm +
    (k^6 - 9*k^5 + 40*k^4 - 103*k^3 + 145*k^2 - 86*k) * v.D +
    (k^5 - 7*k^4 + 23*k^3 - 36*k^2 + 22*k) * v.Dm +
    (k^7 - 14*k^6 + 88*k^5 - 324*k^4 + 726*k^3 - 916*k^2 + 496*k) * v.E +
    (k^6 - 10*k^5 + 45*k^4 - 110*k^3 + 142*k^2 - 76*k) * v.E1 +
    (k^6 - 10*k^5 + 47*k^4 - 122*k^3 + 167*k^2 - 94*k) * v.E2 +
    (k^6 - 10*k^5 + 48*k^4 - 129*k^3 + 185*k^2 - 110*k) * v.E3

/-- `F ∘ step^5` as an explicit linear form -/
def Ge5 (k : ℤ) (v : St) : ℤ :=
  (k^6 - 7*k^5 + 28*k^4 - 65*k^3 + 86*k^2 - 49*k) * v.A +
    (k^7 - 10*k^6 + 51*k^5 - 161*k^4 + 319*k^3 - 366*k^2 + 184*k) * v.B +
    (k^6 - 8*k^5 + 35*k^4 - 88*k^3 + 122*k^2 - 71*k) * v.Bm +
    (k^7 - 11*k^6 + 61*k^5 - 207*k^4 + 437*k^3 - 529*k^2 + 278*k) * v.C +
    (k^6 - 9*k^5 + 42*k^4 - 109*k^3 + 152*k^2 - 88*k) * v.Cm +
    (k^7 - 11*k^6 + 61*k^5 - 207*k^4 + 437*k^3 - 529*k^2 + 278*k) * v.D +
    (k^6 - 9*k^5 + 40*k^4 - 97*k^3 + 124*k^2 - 65*k) * v.Dm +
    (k^8 - 16*k^7 + 119*k^6 - 539*k^5 + 1589*k^4 - 3003*k^3 + 3310*k^2 - 1608*k) * v.E +
    (k^7 - 12*k^6 + 68*k^5 - 224*k^4 + 440*k^3 - 480*k^2 + 224*k) * v.E1 +
    (k^7 - 12*k^6 + 70*k^5 - 241*k^4 + 499*k^3 - 577*k^2 + 286*k) * v.E2 +
    (k^7 - 12*k^6 + 71*k^5 - 252*k^4 + 547*k^3 - 671*k^2 + 354*k) * v.E3

/-- `F ∘ step^6` as an explicit linear form -/
def Ge6 (k : ℤ) (v : St) : ℤ :=
  (k^7 - 9*k^6 + 45*k^5 - 139*k^4 + 275*k^3 - 319*k^2 + 164*k) * v.A +
    (k^8 - 12*k^7 + 74*k^6 - 290*k^5 + 760*k^4 - 1306*k^3 + 1331*k^2 - 606*k) * v.B +
    (k^7 - 10*k^6 + 54*k^5 - 179*k^4 + 372*k^3 - 443*k^2 + 229*k) * v.Bm +
    (k^8 - 13*k^7 + 86*k^6 - 359*k^5 + 997*k^4 - 1807*k^3 + 1935*k^2 - 922*k) * v.C +
    (k^7 - 11*k^6 + 63*k^5 - 217*k^4 + 459*k^3 - 549*k^2 + 283*k) * v.Cm +
    (k^8 - 13*k^7 + 86*k^6 - 359*k^5 + 997*k^4 - 1807*k^3 + 1935*k^2 - 922*k) * v.D +
    (k^7 - 11*k^6 + 61*k^5 - 199*k^4 + 390*k^3 - 425*k^2 + 198*k) * v.Dm +
    (k^9 - 18*k^8 + 154*k^7 - 822*k^6 + 2972*k^5 - 7384*k^4 + 12166*k^3 - 11972*k^2 + 5296*k) * v.E +
    (k^8 - 14*k^7 + 95*k^6 - 391*k^5 + 1029*k^4 - 1704*k^3 + 1625*k^2 - 682*k) * v.E1 +
    (k^8 - 14*k^7 + 97*k^6 - 414*k^5 + 1145*k^4 - 2014*k^3 + 2052*k^2 - 920*k) * v.E2 +
    (k^8 - 14*k^7 + 98*k^6 - 427*k^5 + 1221*k^4 - 2247*k^3 + 2415*k^2 - 1146*k) * v.E3

/-- `F ∘ step^7` as an explicit linear form -/
def Ge7 (k : ℤ) (v : St) : ℤ :=
  (k^8 - 11*k^7 + 66*k^6 - 253*k^5 + 659*k^4 - 1142*k^3 + 1191*k^2 - 560*k) * v.A +
    (k^9 - 14*k^8 + 101*k^7 - 471*k^6 + 1524*k^5 - 3457*k^4 + 5282*k^3 - 4877*k^2 + 2042*k) * v.B +
    (k^8 - 12*k^7 + 77*k^6 - 314*k^5 + 858*k^4 - 1532*k^3 + 1616*k^2 - 758*k) * v.Bm +
    (k^9 - 15*k^8 + 115*k^7 - 567*k^6 + 1932*k^5 - 4598*k^4 + 7349*k^3 - 7081*k^2 + 3086*k) * v.C +
    (k^8 - 13*k^7 + 88*k^6 - 373*k^5 + 1042*k^4 - 1875*k^3 + 1972*k^2 - 917*k) * v.Cm +
    (k^9 - 15*k^8 + 115*k^7 - 567*k^6 + 1932*k^5 - 4598*k^4 + 7349*k^3 - 7081*k^2 + 3086*k) * v.D +
    (k^8 - 13*k^7 + 86*k^6 - 351*k^5 + 928*k^4 - 1555*k^3 + 1503*k^2 - 637*k) * v.Dm +
    (k^10 - 20*k^9 + 193*k^8 - 1181*k^7 + 5022*k^6 - 15298*k^5 + 33125*k^4 - 48643*k^3 + 43382*k^2 - 17640*k) * v.E +
    (k^9 - 16*k^8 + 126*k^7 - 620*k^6 + 2044*k^5 - 4556*k^4 + 6627*k^3 - 5695*k^2 + 2194*k) * v.E1 +
    (k^9 - 16*k^8 + 128*k^7 - 647*k^6 + 2215*k^5 - 5180*k^4 + 7969*k^3 - 7276*k^2 + 2980*k) * v.E2 +
    (k^9 - 16*k^8 + 129*k^7 - 662*k^6 + 2323*k^5 - 5627*k^4 + 9053*k^3 - 8706*k^2 + 3768*k) * v.E3

/-- `F ∘ step^8` as an explicit linear form -/
def Ge8 (k : ℤ) (v : St) : ℤ :=
  (k^9 - 13*k^8 + 91*k^7 - 415*k^6 + 1328*k^5 - 3011*k^4 + 4652*k^3 - 4387*k^2 + 1889*k) * v.A +
    (k^10 - 16*k^9 + 132*k^8 - 712*k^7 + 2725*k^6 - 7599*k^5 + 15272*k^4 - 21040*k^3 + 17744*k^2 - 6864*k) * v.B +
    (k^9 - 14*k^8 + 104*k^7 - 501*k^6 + 1679*k^5 - 3939*k^4 + 6207*k^3 - 5890*k^2 + 2526*k) * v.Bm +
    (k^10 - 17*k^9 + 148*k^8 - 839*k^7 + 3364*k^6 - 9798*k^5 + 20514*k^4 - 29385*k^3 + 25729*k^2 - 10318*k) * v.C +
    (k^9 - 15*k^8 + 117*k^7 - 585*k^6 + 2009*k^5 - 4769*k^4 + 7521*k^3 - 7090*k^2 + 3010*k) * v.Cm +
    (k^10 - 17*k^9 + 148*k^8 - 839*k^7 + 3364*k^6 - 9798*k^5 + 20514*k^4 - 29385*k^3 + 25729*k^2 - 10318*k) * v.D +
    (k^9 - 15*k^8 + 115*k^7 - 559*k^6 + 1842*k^5 - 4138*k^4 + 6094*k^3 - 5304*k^2 + 2063*k) * v.Dm +
    (k^11 - 22*k^10 + 236*k^9 - 1624*k^8 + 7901*k^7 - 28276*k^6 + 75004*k^5 - 144566*k^4 + 191912*k^3 - 156616*k^2 + 58912*k) * v.E +
    (k^10 - 18*k^9 + 161*k^8 - 917*k^7 + 3607*k^6 - 10037*k^5 + 19550*k^4 - 25461*k^3 + 19947*k^2 - 7106*k) * v.E1 +
    (k^10 - 18*k^9 + 163*k^8 - 948*k^7 + 3841*k^6 - 11110*k^5 + 22686*k^4 - 31185*k^3 + 25896*k^2 - 9788*k) * v.E2 +
    (k^10 - 18*k^9 + 164*k^8 - 965*k^7 + 3984*k^6 - 11842*k^5 + 25070*k^4 - 36012*k^3 + 31424*k^2 - 12512*k) * v.E3

/-- `F ∘ step^9` as an explicit linear form -/
def Ge9 (k : ℤ) (v : St) : ℤ :=
  (k^10 - 15*k^9 + 120*k^8 - 633*k^7 + 2390*k^6 - 6628*k^5 + 13365*k^4 - 18639*k^3 + 16038*k^2 - 6366*k) * v.A +
    (k^11 - 18*k^10 + 167*k^9 - 1021*k^8 + 4495*k^7 - 14772*k^6 + 36419*k^5 - 65883*k^4 + 82701*k^3 - 64171*k^2 + 23050*k) * v.B +
    (k^10 - 16*k^9 + 135*k^8 - 748*k^7 + 2949*k^6 - 8470*k^5 + 17503*k^4 - 24733*k^3 + 21342*k^2 - 8429*k) * v.Bm +
    (k^11 - 19*k^10 + 185*k^9 - 1183*k^8 + 5433*k^7 - 18580*k^6 + 47570*k^5 - 89230*k^4 + 116026*k^3 - 93196*k^2 + 34624*k) * v.C +
    (k^10 - 17*k^9 + 150*k^8 - 861*k^7 + 3483*k^6 - 10163*k^5 + 21131*k^4 - 29805*k^3 + 25534*k^2 - 9986*k) * v.Cm +
    (k^11 - 19*k^10 + 185*k^9 - 1183*k^8 + 5433*k^7 - 18580*k^6 + 47570*k^5 - 89230*k^4 + 116026*k^3 - 93196*k^2 + 34624*k) * v.D +
    (k^10 - 17*k^9 + 148*k^8 - 831*k^7 + 3256*k^6 - 9101*k^5 + 17917*k^4 - 23664*k^3 + 18806*k^2 - 6778*k) * v.Dm +
    (k^12 - 24*k^11 + 283*k^10 - 2159*k^9 + 11789*k^8 - 48213*k^7 + 150166*k^6 - 354514*k^5 + 617512*k^4 - 749212*k^3 + 564024*k^2 - 197408*k) * v.E +
    (k^11 - 20*k^10 + 200*k^9 - 1290*k^8 + 5866*k^7 - 19454*k^6 + 47229*k^5 - 82184*k^4 + 97319*k^3 - 70286*k^2 + 23344*k) * v.E1 +
    (k^11 - 20*k^10 + 202*k^9 - 1325*k^8 + 6170*k^7 - 21113*k^6 + 53299*k^5 - 97137*k^4 + 121156*k^3 - 92478*k^2 + 32484*k) * v.E2 +
    (k^11 - 20*k^10 + 203*k^9 - 1344*k^8 + 6350*k^7 - 22187*k^6 + 57607*k^5 - 108780*k^4 + 141487*k^3 - 113143*k^2 + 41730*k) * v.E3

/-- `F ∘ step^10` as an explicit linear form -/
def Ge10 (k : ℤ) (v : St) : ℤ :=
  (k^11 - 17*k^10 + 153*k^9 - 915*k^8 + 3969*k^7 - 12934*k^6 + 31841*k^5 - 57948*k^4 + 73723*k^3 - 58352*k^2 + 21480*k) * v.A +
    (k^12 - 20*k^11 + 206*k^10 - 1406*k^9 + 6982*k^8 - 26305*k^7 + 76289*k^6 - 169200*k^5 + 278849*k^4 - 321824*k^3 + 231380*k^2 - 77584*k) * v.B +
    (k^11 - 18*k^10 + 170*k^9 - 1063*k^8 + 4800*k^7 - 16190*k^6 + 40942*k^5 - 75865*k^4 + 97387*k^3 - 77158*k^2 + 28258*k) * v.Bm +
    (k^12 - 21*k^11 + 226*k^10 - 1607*k^9 + 8295*k^8 - 32419*k^7 + 97360*k^6 - 223296*k^5 + 380215*k^4 - 453166*k^3 + 336371*k^2 - 116390*k) * v.C +
    (k^11 - 19*k^10 + 187*k^9 - 1209*k^8 + 5602*k^7 - 19238*k^6 + 49137*k^5 - 91277*k^4 + 116754*k^3 - 91801*k^2 + 33301*k) * v.Cm +
    (k^12 - 21*k^11 + 226*k^10 - 1607*k^9 + 8295*k^8 - 32419*k^7 + 97360*k^6 - 223296*k^5 + 380215*k^4 - 453166*k^3 + 336371*k^2 - 116390*k) * v.D +
    (k^11 - 19*k^10 + 185*k^9 - 1175*k^8 + 5309*k^7 - 17630*k^6 + 43136*k^5 - 76006*k^4 + 91351*k^3 - 66944*k^2 + 22498*k) * v.Dm +
    (k^13 - 26*k^12 + 334*k^11 - 2794*k^10 + 16882*k^9 - 77388*k^8 + 275249*k^7 - 762902*k^6 + 1627913*k^5 - 2591538*k^4 + 2898247*k^3 - 2025898*k^2 + 662968*k) * v.E +
    (k^12 - 22*k^11 + 243*k^10 - 1747*k^9 + 8984*k^8 - 34418*k^7 + 99509*k^6 - 215577*k^5 + 340500*k^4 - 370802*k^3 + 248864*k^2 - 77480*k) * v.E1 +
    (k^12 - 22*k^11 + 245*k^10 - 1786*k^9 + 9364*k^8 - 36792*k^7 + 109800*k^6 - 247158*k^5 + 408088*k^4 - 466796*k^3 + 330046*k^2 - 108332*k) * v.E2 +
    (k^12 - 22*k^11 + 246*k^10 - 1807*k^9 + 9585*k^8 - 38285*k^7 + 116814*k^6 - 270525*k^5 + 462399*k^4 - 550485*k^3 + 406657*k^2 - 139734*k) * v.E3

lemma Ge_base {k : ℕ} (he : eps k = 1) (v : St) : F k v = Ge0 (k : ℤ) v := by
  unfold F Rm Rx Sxx Snm Sxm Sym Ge0; rw [he]; push_cast; ring

lemma Ge_chain0 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge0 (k : ℤ) (step k v) = Ge1 (k : ℤ) v := by
  unfold Ge0 Ge1 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Ge_chain1 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge1 (k : ℤ) (step k v) = Ge2 (k : ℤ) v := by
  unfold Ge1 Ge2 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Ge_chain2 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge2 (k : ℤ) (step k v) = Ge3 (k : ℤ) v := by
  unfold Ge2 Ge3 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Ge_chain3 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge3 (k : ℤ) (step k v) = Ge4 (k : ℤ) v := by
  unfold Ge3 Ge4 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Ge_chain4 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge4 (k : ℤ) (step k v) = Ge5 (k : ℤ) v := by
  unfold Ge4 Ge5 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Ge_chain5 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge5 (k : ℤ) (step k v) = Ge6 (k : ℤ) v := by
  unfold Ge5 Ge6 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Ge_chain6 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge6 (k : ℤ) (step k v) = Ge7 (k : ℤ) v := by
  unfold Ge6 Ge7 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Ge_chain7 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge7 (k : ℤ) (step k v) = Ge8 (k : ℤ) v := by
  unfold Ge7 Ge8 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Ge_chain8 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge8 (k : ℤ) (step k v) = Ge9 (k : ℤ) v := by
  unfold Ge8 Ge9 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma Ge_chain9 {k : ℕ} (he : eps k = 1) (v : St) :
    Ge9 (k : ℤ) (step k v) = Ge10 (k : ℤ) v := by
  unfold Ge9 Ge10 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

/-- `F ∘ step^0` as an explicit linear form -/
def G1_0 (v : St) : ℤ :=
  (2) * v.A

/-- `F ∘ step^1` as an explicit linear form -/
def G1_1 (v : St) : ℤ :=
  (2) * v.A

lemma G1__base (he : eps 1 = 0) (v : St) : F 1 v = G1_0 v := by
  unfold F Rm Rx Sxx Snm Sxm Sym G1_0; rw [he]; push_cast; ring

lemma G1__chain0 (he : eps 1 = 0) (v : St) :
    G1_0 (step 1 v) = G1_1 v := by
  unfold G1_0 G1_1 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

/-- `F ∘ step^0` as an explicit linear form -/
def G2_0 (v : St) : ℤ :=
  (2) * v.A +
    (2) * v.Bm +
    (2) * v.Cm +
    (2) * v.Dm

/-- `F ∘ step^1` as an explicit linear form -/
def G2_1 (v : St) : ℤ :=
  (4) * v.A +
    (2) * v.Bm +
    (2) * v.Cm +
    (2) * v.Dm

/-- `F ∘ step^2` as an explicit linear form -/
def G2_2 (v : St) : ℤ :=
  (6) * v.A +
    (4) * v.Bm +
    (2) * v.Cm +
    (2) * v.Dm

/-- `F ∘ step^3` as an explicit linear form -/
def G2_3 (v : St) : ℤ :=
  (8) * v.A +
    (6) * v.Bm +
    (4) * v.Cm +
    (2) * v.Dm

/-- `F ∘ step^4` as an explicit linear form -/
def G2_4 (v : St) : ℤ :=
  (10) * v.A +
    (8) * v.Bm +
    (6) * v.Cm +
    (4) * v.Dm

lemma G2__base (he : eps 2 = 1) (v : St) : F 2 v = G2_0 v := by
  unfold F Rm Rx Sxx Snm Sxm Sym G2_0; rw [he]; push_cast; ring

lemma G2__chain0 (he : eps 2 = 1) (v : St) :
    G2_0 (step 2 v) = G2_1 v := by
  unfold G2_0 G2_1 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G2__chain1 (he : eps 2 = 1) (v : St) :
    G2_1 (step 2 v) = G2_2 v := by
  unfold G2_1 G2_2 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G2__chain2 (he : eps 2 = 1) (v : St) :
    G2_2 (step 2 v) = G2_3 v := by
  unfold G2_2 G2_3 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G2__chain3 (he : eps 2 = 1) (v : St) :
    G2_3 (step 2 v) = G2_4 v := by
  unfold G2_3 G2_4 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

/-- `F ∘ step^0` as an explicit linear form -/
def G3_0 (v : St) : ℤ :=
  (4) * v.A +
    (8) * v.B +
    (8) * v.C +
    (8) * v.D

/-- `F ∘ step^1` as an explicit linear form -/
def G3_1 (v : St) : ℤ :=
  (12) * v.A +
    (16) * v.B +
    (16) * v.C +
    (16) * v.D

/-- `F ∘ step^2` as an explicit linear form -/
def G3_2 (v : St) : ℤ :=
  (28) * v.A +
    (40) * v.B +
    (32) * v.C +
    (32) * v.D

/-- `F ∘ step^3` as an explicit linear form -/
def G3_3 (v : St) : ℤ :=
  (60) * v.A +
    (88) * v.B +
    (72) * v.C +
    (72) * v.D

lemma G3__base (he : eps 3 = 0) (v : St) : F 3 v = G3_0 v := by
  unfold F Rm Rx Sxx Snm Sxm Sym G3_0; rw [he]; push_cast; ring

lemma G3__chain0 (he : eps 3 = 0) (v : St) :
    G3_0 (step 3 v) = G3_1 v := by
  unfold G3_0 G3_1 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G3__chain1 (he : eps 3 = 0) (v : St) :
    G3_1 (step 3 v) = G3_2 v := by
  unfold G3_1 G3_2 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G3__chain2 (he : eps 3 = 0) (v : St) :
    G3_2 (step 3 v) = G3_3 v := by
  unfold G3_2 G3_3 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

/-- `F ∘ step^0` as an explicit linear form -/
def G4_0 (v : St) : ℤ :=
  (4) * v.A +
    (8) * v.B +
    (4) * v.Bm +
    (8) * v.C +
    (4) * v.Cm +
    (8) * v.D +
    (4) * v.Dm +
    (8) * v.E1 +
    (8) * v.E2 +
    (8) * v.E3

/-- `F ∘ step^1` as an explicit linear form -/
def G4_1 (v : St) : ℤ :=
  (16) * v.A +
    (24) * v.B +
    (12) * v.Bm +
    (24) * v.C +
    (12) * v.Cm +
    (24) * v.D +
    (12) * v.Dm +
    (16) * v.E1 +
    (16) * v.E2 +
    (16) * v.E3

/-- `F ∘ step^2` as an explicit linear form -/
def G4_2 (v : St) : ℤ :=
  (52) * v.A +
    (80) * v.B +
    (40) * v.Bm +
    (64) * v.C +
    (28) * v.Cm +
    (64) * v.D +
    (28) * v.Dm +
    (40) * v.E1 +
    (40) * v.E2 +
    (48) * v.E3

/-- `F ∘ step^3` as an explicit linear form -/
def G4_3 (v : St) : ℤ :=
  (144) * v.A +
    (224) * v.B +
    (116) * v.Bm +
    (184) * v.C +
    (88) * v.Cm +
    (184) * v.D +
    (68) * v.Dm +
    (96) * v.E1 +
    (128) * v.E2 +
    (144) * v.E3

/-- `F ∘ step^4` as an explicit linear form -/
def G4_4 (v : St) : ℤ :=
  (396) * v.A +
    (608) * v.B +
    (328) * v.Bm +
    (504) * v.C +
    (260) * v.Cm +
    (504) * v.D +
    (216) * v.Dm +
    (304) * v.E1 +
    (376) * v.E2 +
    (408) * v.E3

/-- `F ∘ step^5` as an explicit linear form -/
def G4_5 (v : St) : ℤ :=
  (1116) * v.A +
    (1728) * v.B +
    (900) * v.Bm +
    (1416) * v.C +
    (736) * v.Cm +
    (1416) * v.D +
    (636) * v.Dm +
    (896) * v.E1 +
    (1064) * v.E2 +
    (1112) * v.E3

/-- `F ∘ step^6` as an explicit linear form -/
def G4_6 (v : St) : ℤ :=
  (3168) * v.A +
    (4920) * v.B +
    (2532) * v.Bm +
    (4040) * v.C +
    (2012) * v.Cm +
    (4040) * v.D +
    (1800) * v.Dm +
    (2536) * v.E1 +
    (2912) * v.E2 +
    (3144) * v.E3

/-- `F ∘ step^7` as an explicit linear form -/
def G4_7 (v : St) : ℤ :=
  (9008) * v.A +
    (13976) * v.B +
    (7208) * v.Bm +
    (11496) * v.C +
    (5676) * v.Cm +
    (11496) * v.D +
    (4924) * v.Dm +
    (6936) * v.E1 +
    (8208) * v.E2 +
    (8960) * v.E3

/-- `F ∘ step^8` as an explicit linear form -/
def G4_8 (v : St) : ℤ :=
  (25428) * v.A +
    (39360) * v.B +
    (20504) * v.Bm +
    (32408) * v.C +
    (16168) * v.Cm +
    (32408) * v.D +
    (13884) * v.Dm +
    (19560) * v.E1 +
    (23376) * v.E2 +
    (25472) * v.E3

/-- `F ∘ step^9` as an explicit linear form -/
def G4_9 (v : St) : ℤ :=
  (71720) * v.A +
    (111032) * v.B +
    (57836) * v.Bm +
    (91328) * v.C +
    (45976) * v.Cm +
    (91328) * v.D +
    (39544) * v.Dm +
    (55712) * v.E1 +
    (66480) * v.E2 +
    (71768) * v.E3

lemma G4__base (he : eps 4 = 1) (v : St) : F 4 v = G4_0 v := by
  unfold F Rm Rx Sxx Snm Sxm Sym G4_0; rw [he]; push_cast; ring

lemma G4__chain0 (he : eps 4 = 1) (v : St) :
    G4_0 (step 4 v) = G4_1 v := by
  unfold G4_0 G4_1 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G4__chain1 (he : eps 4 = 1) (v : St) :
    G4_1 (step 4 v) = G4_2 v := by
  unfold G4_1 G4_2 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G4__chain2 (he : eps 4 = 1) (v : St) :
    G4_2 (step 4 v) = G4_3 v := by
  unfold G4_2 G4_3 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G4__chain3 (he : eps 4 = 1) (v : St) :
    G4_3 (step 4 v) = G4_4 v := by
  unfold G4_3 G4_4 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G4__chain4 (he : eps 4 = 1) (v : St) :
    G4_4 (step 4 v) = G4_5 v := by
  unfold G4_4 G4_5 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G4__chain5 (he : eps 4 = 1) (v : St) :
    G4_5 (step 4 v) = G4_6 v := by
  unfold G4_5 G4_6 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G4__chain6 (he : eps 4 = 1) (v : St) :
    G4_6 (step 4 v) = G4_7 v := by
  unfold G4_6 G4_7 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G4__chain7 (he : eps 4 = 1) (v : St) :
    G4_7 (step 4 v) = G4_8 v := by
  unfold G4_7 G4_8 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

lemma G4__chain8 (he : eps 4 = 1) (v : St) :
    G4_8 (step 4 v) = G4_9 v := by
  unfold G4_8 G4_9 step Sxx Snm Sxm Sym; simp only; rw [he]; push_cast; ring

end A246479
