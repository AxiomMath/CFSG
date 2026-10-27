module

public import Certificates.Data.GHarrisA5Data

public section

namespace CertificateChecks.KernelGHarrisA5

open CFSG.ComponentClassification.GHarris

theorem orbit_ok :
    ∀ k ∈ List.range 70, (GL42.witAt k).isOrbit = true → k ∈ GL42.orbitKs := by
  decide +kernel

abbrev WordsOK (k : ℕ) : Prop :=
  GL42.a5Idx k < 4 ∧
    (∀ e ∈ GL42.e0c, e ∈ GL42.a5At (GL42.a5Idx k)) ∧
    (∀ c ∈ GL42.conjAt k, c ∈ GL42.a5At (GL42.a5Idx k)) ∧
    (GL42.a5At (GL42.a5Idx k)).length = 60 ∧
    ∀ i ∈ List.range 60, GL42.wordProd (GL42.e0c ++ GL42.conjAt k) ((GL42.wordsAt k).getD i []) =
      (GL42.a5At (GL42.a5Idx k)).getD i GL42.M4c.one

abbrev PairsOK (k : ℕ) : Prop :=
  ∀ k' ∈ GL42.orbitKs, GL42.a5Idx k ≠ GL42.a5Idx k' →
    GL42.IsOrder4 (GL42.wordProd (GL42.e0c ++ GL42.conjAt k ++ GL42.conjAt k')
      (GL42.pairWord k k'))

theorem w1 : WordsOK 1 := by decide +kernel
theorem w2 : WordsOK 2 := by decide +kernel
theorem w3 : WordsOK 3 := by decide +kernel
theorem w4 : WordsOK 4 := by decide +kernel
theorem w9 : WordsOK 9 := by decide +kernel
theorem w10 : WordsOK 10 := by decide +kernel
theorem w11 : WordsOK 11 := by decide +kernel
theorem w12 : WordsOK 12 := by decide +kernel
theorem w17 : WordsOK 17 := by decide +kernel
theorem w18 : WordsOK 18 := by decide +kernel
theorem w19 : WordsOK 19 := by decide +kernel
theorem w20 : WordsOK 20 := by decide +kernel
theorem w25 : WordsOK 25 := by decide +kernel
theorem w26 : WordsOK 26 := by decide +kernel
theorem w27 : WordsOK 27 := by decide +kernel
theorem w28 : WordsOK 28 := by decide +kernel

theorem p1 : PairsOK 1 := by decide +kernel
theorem p2 : PairsOK 2 := by decide +kernel
theorem p3 : PairsOK 3 := by decide +kernel
theorem p4 : PairsOK 4 := by decide +kernel
theorem p9 : PairsOK 9 := by decide +kernel
theorem p10 : PairsOK 10 := by decide +kernel
theorem p11 : PairsOK 11 := by decide +kernel
theorem p12 : PairsOK 12 := by decide +kernel
theorem p17 : PairsOK 17 := by decide +kernel
theorem p18 : PairsOK 18 := by decide +kernel
theorem p19 : PairsOK 19 := by decide +kernel
theorem p20 : PairsOK 20 := by decide +kernel
theorem p25 : PairsOK 25 := by decide +kernel
theorem p26 : PairsOK 26 := by decide +kernel
theorem p27 : PairsOK 27 := by decide +kernel
theorem p28 : PairsOK 28 := by decide +kernel

theorem orbitKs_cases {P : ℕ → Prop} (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h9 : P 9)
    (h10 : P 10) (h11 : P 11) (h12 : P 12) (h17 : P 17) (h18 : P 18) (h19 : P 19) (h20 : P 20)
    (h25 : P 25) (h26 : P 26) (h27 : P 27) (h28 : P 28) : ∀ k ∈ GL42.orbitKs, P k := by
  intro k hk
  simp only [GL42.orbitKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  exacts [h1, h2, h3, h4, h9, h10, h11, h12, h17, h18, h19, h20, h25, h26, h27, h28]

theorem words_ok : ∀ k ∈ GL42.orbitKs, WordsOK k :=
  orbitKs_cases w1 w2 w3 w4 w9 w10 w11 w12 w17 w18 w19 w20 w25 w26 w27 w28

theorem pairs_ok : ∀ k ∈ GL42.orbitKs, PairsOK k :=
  orbitKs_cases p1 p2 p3 p4 p9 p10 p11 p12 p17 p18 p19 p20 p25 p26 p27 p28

end CertificateChecks.KernelGHarrisA5

end
