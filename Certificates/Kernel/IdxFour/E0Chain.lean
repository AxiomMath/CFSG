module

public import Certificates.Kernel.IdxFour.E0Rec0
public import Certificates.Kernel.IdxFour.E0Rec1
public import Certificates.Kernel.IdxFour.E0Lvl
public import CFSG.Certificates.Kernel.IdxFourChainCard
public import CFSG.GF2Type.Smith1979.IdxFourModelDefs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4E

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour

theorem gens_spec : tlOK SP B TL 10 1 = true ∧ tlOK SP B TL 10 2 = true ∧
    tlOK SP B TL 10 3 = true ∧ tlOK SP B TL 10 4 = true ∧ invOK SP SI 10 = true ∧
    wordsOK SP SI 10 WD 3 = true := by
  have h := cf17601gens
  unfold gens at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem lvl_spec {i : Nat} (hi : i < 5) :
    cntOK O TL R i = true ∧ treeOK SP T O TL TR i = true ∧ posOK T O PS B i = true := by
  have h : lvl i = true := by
    interval_cases i
    exacts [cf17601lv0, cf17601lv1, cf17601lv2, cf17601lv3, cf17601lv4]
  unfold lvl at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem blk_spec {i : Nat} (hi : i < 5) (c : Nat) (hc : 32 * c < (R.getD i []).length) :
    blkOK SP T O TL R i c = true := by
  change blk i c = true
  interval_cases i
  · have : (R.getD 0 []).length = 1134 := by decide +kernel
    exact cf17601r0all c (by omega : c < 36)
  · have : (R.getD 1 []).length = 560 := by decide +kernel
    exact cf17601r1all c (by omega : c < 18)
  · have : (R.getD 2 []).length = 48 := by decide +kernel
    exact cf17601r2all c (by omega : c < 2)
  · have : (R.getD 3 []).length = 18 := by decide +kernel
    exact cf17601r3all c (by omega : c < 1)
  · have : (R.getD 4 []).length = 3 := by decide +kernel
    exact cf17601r4all c (by omega : c < 1)

theorem e0ChainHyp : ChainHyp SP SI T O PS B TL WD TR R 5 3 10 where
  lenO := by decide +kernel
  lenT := by decide +kernel
  tl0 := by decide +kernel
  tlk := by decide +kernel
  tl i h1 h5 := by
    obtain ⟨h1', h2, h3, h4, -, -⟩ := gens_spec
    interval_cases i
    exacts [h1', h2, h3, h4]
  inv := gens_spec.2.2.2.2.1
  words := gens_spec.2.2.2.2.2
  tree i hi := (lvl_spec hi).2.1
  pos i hi := (lvl_spec hi).2.2
  cnt i hi := (lvl_spec hi).1
  blk i hi c hc := blk_spec hi c hc

theorem rowsP_gens : rowsP (look SP 0) = a3Rows ∧ rowsP (look SP 1) = a5Rows ∧
    rowsP (look SP 2) = y3Rows := by
  decide +kernel

theorem lvlGrp_zero_eq_E0 : lvlGrp SP TL 0 = E0 := by
  have hTL : TL.getD 0 [] = [0, 1, 2] := by decide +kernel
  obtain ⟨h0, h1, h2⟩ := rowsP_gens
  rw [lvlGrp, E0, Viol.genGrp, hTL]
  congr 1
  ext U
  simp only [Set.mem_setOf_eq, Viol.GenSet, e0Gens, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, IsP, linP_eq_of_rowsP h0, linP_eq_of_rowsP h1,
    linP_eq_of_rowsP h2]

theorem card_E0 : Nat.card E0 = 9797760 := by
  rw [← lvlGrp_zero_eq_E0, e0ChainHyp.card_zero]
  decide +kernel

theorem eq_one_of_fix_base {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ E0)
    (hfix : ∀ b ∈ [12, 20, 264, 36, 63], U (vecOf b) = vecOf b) : U = 1 := by
  rw [← lvlGrp_zero_eq_E0] at hU
  have hB : B = [12, 20, 264, 36, 63] := by decide +kernel
  refine e0ChainHyp.eq_one_of_fix hU fun q hq => hfix _ ?_
  rw [hB]
  interval_cases q <;> simp

end CFSG.KD.IF4E

end
