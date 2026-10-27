module

public import Certificates.Kernel.IdxFour.SaLvl
public import CFSG.Certificates.Kernel.IdxFourChainCard
public import CFSG.GF2Type.Smith1979.IdxFourModelData
public import CFSG.GF2Type.Smith1979.GammaU.Violation

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4S

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour

theorem gens_spec : tlOK SP B TL 9 1 = true ∧ tlOK SP B TL 9 2 = true ∧
    tlOK SP B TL 9 3 = true ∧ tlOK SP B TL 9 4 = true ∧ tlOK SP B TL 9 5 = true ∧
    invOK SP SI 9 = true ∧ wordsOK SP SI 9 WD 3 = true := by
  have h := cf17607gens
  unfold gens at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem lvl_spec {i : Nat} (hi : i < 6) :
    treeOK SP T O TL TR i = true ∧ posOK T O PS B i = true := by
  have h : lvl i = true := by
    interval_cases i
    exacts [cf17607lv0, cf17607lv1, cf17607lv2, cf17607lv3, cf17607lv4, cf17607lv5]
  unfold lvl at h
  simpa only [Bool.and_eq_true] using h

theorem saTreeHyp : TreeHyp SP SI T O PS B TL WD TR 6 3 9 where
  lenO := by decide +kernel
  tl0 := by decide +kernel
  tlk := by decide +kernel
  tl i h1 h6 := by
    obtain ⟨h1', h2, h3, h4, h5, -, -⟩ := gens_spec
    interval_cases i
    exacts [h1', h2, h3, h4, h5]
  inv := gens_spec.2.2.2.2.2.1
  words := gens_spec.2.2.2.2.2.2
  tree i hi := (lvl_spec hi).1
  pos i hi := (lvl_spec hi).2

theorem rowsP_gens : rowsP (look SP 0) = sGens[0]! ∧ rowsP (look SP 1) = sGens[1]! ∧
    rowsP (look SP 2) = sGens[2]! := by
  decide +kernel

theorem lvlGrp_zero_eq_sGens : lvlGrp SP TL 0 = Viol.genGrp sGens := by
  have hTL : TL.getD 0 [] = [0, 1, 2] := by decide +kernel
  have hs : sGens = [sGens[0]!, sGens[1]!, sGens[2]!] := by decide +kernel
  obtain ⟨h0, h1, h2⟩ := rowsP_gens
  rw [lvlGrp, Viol.genGrp, hTL, hs]
  congr 1
  ext U
  simp only [Set.mem_setOf_eq, Viol.GenSet, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, IsP, linP_eq_of_rowsP h0, linP_eq_of_rowsP h1,
    linP_eq_of_rowsP h2]

theorem le_card_genGrp_sGens : 23040 ≤ Nat.card (Viol.genGrp sGens) := by
  rw [← lvlGrp_zero_eq_sGens]
  have h := saTreeHyp.prod_le_card
  have hO : O.prod = 23040 := by decide +kernel
  rwa [hO] at h

end CFSG.KD.IF4S

end
