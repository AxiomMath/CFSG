
module

public import CFSG.Certificates.Kernel.WE8KSound
public import Certificates.Kernel.WE8K.Checks
public import Certificates.Kernel.WE8K.TabChecks
public import CFSG.RankThree.Chevalley.SteinbergBIWE8ClassesBase

public noncomputable section

namespace CFSG.KD.WE8K

open CFSG.KC.WE8K CFSG.RankThree.Chevalley.WeylE8 CFSG.LieType.Chevalley.WE8.Native

theorem ch18004_nthN_oN : ∀ i < 9, nthN oN i = classSizes.getD i 0 := by
  rw [ch18004_oN]
  decide

theorem ch18004_nthN_oN9 : nthN oN 9 = 15120 := by
  rw [ch18004_oN]
  rfl

theorem ch18004_classSizes_z : ∀ i < 3, classSizes.getD (7 - i) 0 = classSizes.getD i 0 := by
  decide

theorem card_isConj_congr {a b : W8} (h : IsConj a b) :
    Nat.card {u : W8 // IsConj a u} = Nat.card {u : W8 // IsConj b u} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun u => ⟨h.symm.trans, h.trans⟩)

theorem card_isConj_z (t : W8) :
    Nat.card {u : W8 // IsConj (z * t) u} = Nat.card {u : W8 // IsConj t u} := by
  have key : ∀ a u : W8, IsConj a u → IsConj (z * a) (z * u) := fun a u h => by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨c, ?_⟩
    rw [← hc, ← mul_assoc, ← z_mul_comm c]
    group
  refine Nat.card_congr ⟨fun u => ⟨z * u.1, ?_⟩, fun u => ⟨z * u.1, key _ _ u.2⟩,
    fun u => ?_, fun u => ?_⟩
  · have := key _ _ u.2
    rwa [← mul_assoc, z_mul_z, one_mul] at this
  · exact Subtype.ext (by simp only [← mul_assoc, z_mul_z, one_mul])
  · exact Subtype.ext (by simp only [← mul_assoc, z_mul_z, one_mul])

theorem ch18004_lower :
    (∀ i < 9, classSizes.getD i 0 ≤ Nat.card {u : W8 // IsConj (rep i) u}) ∧
      15120 ≤ Nat.card {u : W8 // IsConj y0 u} := by
  obtain ⟨hs, hs9⟩ := startsOK_spec ch18004_starts
  have hkey : ∀ i < 9, nthN oS i = keyI (code (rep i)) := fun i hi => by
    rw [hs i hi, code_rep hi]
  have orb : ∀ i < 9, orbFam i = true → classSizes.getD i 0 ≤ Nat.card {u : W8 // IsConj (rep i) u} :=
    fun i hi ho => by
      change orbOK permP negP addP adjM (nthN oS i) (nthL oL i) (nthN oN i) = true at ho
      rw [hkey i hi, ch18004_nthN_oN i hi] at ho
      exact orbOK_le ch18004_tab (rep i) ho
  have low : ∀ i < 5, classSizes.getD i 0 ≤ Nat.card {u : W8 // IsConj (rep i) u} :=
    fun i hi => orb i (by omega) (ch18004_orbAll i hi)
  refine ⟨fun i hi => ?_, ?_⟩
  · by_cases h5 : i < 5
    · exact low i h5
    by_cases h8 : i = 8
    · subst h8
      exact orb 8 (by omega) ch18004_orb8
    have hz := ch18004_zwAll (7 - i) (show 7 - i < 3 by omega)
    change zwOK permP negP addP adjM (nthN oS (7 - i)) (nthL zW (7 - i))
      (nthN oS (Nat.sub 7 (7 - i))) = true at hz
    have e : Nat.sub 7 (7 - i) = i := by change 7 - (7 - i) = i; omega
    rw [e, hkey (7 - i) (by omega), hkey i hi] at hz
    have hc := zwOK_isConj ch18004_tab z_smul (rep (7 - i)) (rep i) hz
    have e2 : classSizes.getD i 0 = classSizes.getD (7 - i) 0 := by
      have := ch18004_classSizes_z (7 - i) (by omega)
      rwa [show 7 - (7 - i) = i by omega] at this
    rw [card_isConj_congr hc, card_isConj_z, e2]
    exact low (7 - i) (by omega)
  · have ho := ch18004_orb9
    change orbOK permP negP addP adjM (nthN oS 9) (nthL oL 9) (nthN oN 9) = true at ho
    rw [hs9, ← code_y0, ch18004_nthN_oN9] at ho
    exact orbOK_le ch18004_tab y0 ho

theorem ch18004_sumP : ∑ k ∈ Finset.range 21, fld(cp, Nat.shiftLeft k 4, 0xFFFF) = 199952 := by
  decide +kernel

theorem ch18004_sumM : ∑ k ∈ Finset.range 2, fld(cm, Nat.shiftLeft k 4, 0xFFFF) = 15120 := by
  decide +kernel

theorem ch18004_upper :
    Nat.card {w : W8 // SgnSym 1 w} ≤ 199952 ∧ Nat.card {w : W8 // SgnSym (-1) w} ≤ 15120 :=
  ⟨card_sgnSym_le 1 ch18004_tab ch18004_qP (by decide +kernel) (by decide +kernel)
      (by decide +kernel) ch18004_sumP ch18004_symPAll,
    card_sgnSym_le (-1) ch18004_tab ch18004_qM (by decide +kernel) (by decide +kernel)
      (by decide +kernel) ch18004_sumM ch18004_symMAll⟩

end CFSG.KD.WE8K
