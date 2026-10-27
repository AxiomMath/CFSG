module

public import Certificates.Kernel.IdxFour.SkRec
public import Certificates.Kernel.IdxFour.SkLvl
public import Certificates.Kernel.IdxFour.SkFuse
public import Certificates.Kernel.IdxFour.Sift
public import CFSG.Certificates.Kernel.IdxFourFuseSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4K

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4F CFSG.GF2Type.Smith1979.GammaU
  CFSG.GF2Type.Smith1979.IdxFour

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem gens_spec :
    tlOK SP B TL 5 1 = true ∧ invOK SP SI 5 = true ∧ wordsOK SP SI 5 WD 4 = true := by
  have h := cf17612gens
  unfold gens at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lvl_spec {i : Nat} (hi : i < 2) :
    cntOK O TL R i = true ∧ treeOK SP T O TL TR i = true ∧ posOK T O PS B i = true := by
  have h : lvl i = true := by
    interval_cases i
    exacts [cf17612lv0, cf17612lv1]
  unfold lvl at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem blk_spec {i : Nat} (hi : i < 2) (c : Nat) (hc : 32 * c < (R.getD i []).length) :
    blkOK SP T O TL R i c = true := by
  change blk i c = true
  interval_cases i
  · have : (R.getD 0 []).length = 512 := by decide +kernel
    exact cf17612r0all c (by omega : c < 16)
  · have : (R.getD 1 []).length = 2 := by decide +kernel
    have hc0 : c = 0 := by omega
    rw [hc0]
    exact cf17612r1c0

theorem skChainHyp : ChainHyp SP SI T O PS B TL WD TR R 2 4 5 where
  lenO := by decide +kernel
  lenT := by decide +kernel
  tl0 := by decide +kernel
  tlk := by decide +kernel
  tl i h1 h2 := by
    have hi : i = 1 := by omega
    rw [hi]
    exact gens_spec.1
  inv := gens_spec.2.1
  words := gens_spec.2.2
  tree i hi := (lvl_spec hi).2.1
  pos i hi := (lvl_spec hi).2.2
  cnt i hi := (lvl_spec hi).1
  blk i hi c hc := blk_spec hi c hc

theorem O_getD : O.getD 0 0 * O.getD 1 0 = 256 := by decide +kernel

theorem lvlGrp_zero_eq_S : lvlGrp SP TL 0 = Viol.genGrp skGens := by
  have hsk := cf17612sk
  simp only [List.all_eq_true, List.mem_range, Nat.beq_eq] at hsk
  refine lvlGrp_eq_genGrp (j0 := 4) (by decide +kernel) rfl fun j hj => ?_
  rw [hsk j hj]
  have hmem : skGens.getD j #[] ∈ skGens := by
    rw [getD_of_lt _ (by simpa [skGens] using hj)]
    exact List.getElem_mem _
  exact CFSG.KD.IF4R.rowsP_packR _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hmem))))

theorem card_S : Nat.card (Viol.genGrp skGens) = 256 := by
  rw [← lvlGrp_zero_eq_S, skChainHyp.card_zero]
  decide +kernel

theorem S_le_M0 : Viol.genGrp skGens ≤ M0 :=
  CFSG.KD.IF4R.sift17611.2.2.1.trans (sup_le CFSG.KD.IF4M.E0_le_M0 CFSG.KD.IF4R.sift17609.2)

theorem conj_S : ∀ s ∈ Viol.genGrp skGens, s * s = 1 →
    ∃ h ∈ M0, h * s * h⁻¹ ∈ Viol.genGrp lbarGens := by
  intro s hs h2
  rw [← lvlGrp_zero_eq_S] at hs
  obtain ⟨q, hq, hsq⟩ := exists_eltP skChainHyp hs
  refine conj_of_witOK (S := Viol.genGrp skGens) (ET := CFSG.KD.IF4E.T) (EO := CFSG.KD.IF4E.O)
    (Q := CFSG.KD.IF4M.Q) (L := lbarGens.map packR) (W := W) ?_ ?_ ?_ ?_ S_le_M0 ?_ hq hsq h2
  · rw [← lvlGrp_zero_eq_S]
    exact exists_mem_eltP skChainHyp.toTreeHyp
  · intro as hp
    obtain ⟨P, hP, hPP⟩ := CFSG.KD.IF4M.exists_path hp
    exact ⟨P, CFSG.KD.IF4M.E0_le_M0 hP, hPP⟩
  · intro f hf
    obtain ⟨U, hU, hUP, -⟩ := CFSG.KD.IF4M.exists_q f hf
    exact ⟨U, hU, hUP⟩
  · intro g hg
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
    exact CFSG.KD.IF4R.exists_lbar l hl
  · intro q hq
    rw [O_getD] at hq
    have h8 : q / 32 < 8 := by omega
    have hc := fuseBlk_spec (cf17612wall (q / 32) h8) (q % 32) (Nat.mod_lt _ (by omega))
    rwa [Nat.div_add_mod] at hc

end CFSG.KD.IF4K

end
