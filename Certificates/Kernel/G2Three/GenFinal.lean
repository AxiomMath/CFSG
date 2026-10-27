module

public import Certificates.Kernel.G2Three.GenChecks
public import Certificates.Kernel.G2Three.K7bFinal

public section

namespace CFSG.KD.G2Three

open CFSG.KC.G2Three CFSG.RankThree.PartTwo.Census.Carrier.G2Three Certificates.G2ThreeMax
  Certificates.G2Gen

theorem mpow_ok {a : Array ℕ} (ha : canon14 a.toList = true) :
    ∀ n, canon14 (mpowArr a n).toList = true ∧ pk (mpowArr a n).toList = powK (pk a.toList) n
  | 0 => ⟨canon_idArr, pk_idArr⟩
  | n + 1 => by
    refine ⟨canon_mmul _ _, ?_⟩
    rw [mpowArr, pk_mmul ha (mpow_ok ha n).1, (mpow_ok ha n).2]
    rfl

theorem canon_mpow {a : Array ℕ} (ha : canon14 a.toList = true) (n : ℕ) :
    canon14 (mpowArr a n).toList = true := (mpow_ok ha n).1

theorem pk_mpow {a : Array ℕ} (ha : canon14 a.toList = true) (n : ℕ) :
    pk (mpowArr a n).toList = powK (pk a.toList) n := (mpow_ok ha n).2

theorem ent_two {a : Array ℕ} (ha : canon14 a.toList = true) {p : ℕ} (hp : p < 196) :
    (a[p]! % 3 == 2) = Nat.testBit (pk a.toList) (196 + p) := by
  rw [bang_eq, testBit_pk_hi (canon14_iff.1 ha).1 hp]
  have h3 := getD_lt3 ha p
  generalize a.toList.getD p 0 = x at h3 ⊢
  interval_cases x <;> rfl

theorem g2GenCheck_eq : g2GenCheck = g2GenK K7G := by
  simp only [g2GenCheck, g2GenK, beqA, nz_eq, ent_two, canon_mmul, canon_word, canon_idArr,
    canon_mpow, pk_mmul, pk_word, pk_idArr, pk_mpow, (by decide : 2 < 196),
    (by decide : 45 < 196)]

theorem g2GenCheck_ok : g2GenCheck = true := g2GenCheck_eq.trans g2Gen1208102_ok

end CFSG.KD.G2Three

end
