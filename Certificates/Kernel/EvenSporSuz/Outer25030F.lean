module

public import Certificates.Kernel.EvenSporSuz.Outer25030
public import Certificates.Kernel.EvenSporSuz.Fours25010F
public import CFSG.Certificates.Kernel.EvenSporSuz.OuterBlkSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.EvenSporadicStandard.TwoSuz

theorem owLines : outerLines = owW.toArray := by
  unfold outerLines owW
  rw [OW.eq, lines_ofList, List.map_toArray, List.map_map]
  congr 1
  refine List.map_congr_left fun L hL => ?_
  exact outerParseWord_ofList L (List.all_eq_true.1 ch25030M_lines L hL)

theorem lvl1Canon (b : OuterBlock) : CanonGS (outerLvl1 b) := outerSub_canon _ _ _

theorem lvl2Canon (b : OuterBlock) : CanonGS (outerLvl2 b) := outerSub_canon _ _ _

theorem lvl1Mats (b : OuterBlock) : (outerLvl1 b).mats.toList.map rowsOf = L1M b := by
  unfold outerLvl1 L1M
  rw [outerSub_mats lvl0Canon, lvl0Mats, lvl0Invs]

theorem lvl1Invs (b : OuterBlock) : (outerLvl1 b).invs.toList.map rowsOf = L1I b := by
  unfold outerLvl1 L1I
  rw [outerSub_invs lvl0Canon, lvl0Mats, lvl0Invs]

theorem lvl2Mats (b : OuterBlock) : (outerLvl2 b).mats.toList.map rowsOf = L2M b := by
  unfold outerLvl2 L2M
  rw [outerSub_mats (lvl1Canon b), lvl1Mats, lvl1Invs]

theorem lvl2Invs (b : OuterBlock) : (outerLvl2 b).invs.toList.map rowsOf = L2I b := by
  unfold outerLvl2 L2I
  rw [outerSub_invs (lvl1Canon b), lvl1Mats, lvl1Invs]

theorem blockOK_of (i : ℕ) (b : OuterBlock)
    (h1 : validR (L1M b) (L1I b) = true ∧ validR (L2M b) (L2I b) = true)
    (hm : miscK b = true) (hz : zsK b = true)
    (hn : (evalR (L1M b) (L1I b) (b.neg.map zCode) == negR) = true)
    (hc : b.gens.all (fun w => outerCommutesT i w) = true) : outerBlockOK i b = true := by
  have e1 : (outerLvl1 b).valid = true := by
    rw [valid_eq (lvl1Canon b), lvl1Mats, lvl1Invs]
    exact h1.1
  have e2 : (outerLvl2 b).valid = true := by
    rw [valid_eq (lvl2Canon b), lvl2Mats, lvl2Invs]
    exact h1.2
  unfold miscK at hm
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨m1, m2⟩, m3⟩, m4⟩, m5⟩, m6⟩ := hm
  have e3 : b.gens.all (fun w => CFSG.Monster.B.Co2.Native.lettersOK 2 w && outerCommutesT i w) =
      true := by
    simp only [List.all_eq_true] at m3 hc ⊢
    intro w hw
    rw [m3 w hw, hc w hw]
    rfl
  have e9 : (List.range b.gens.length).all (fun s => (outerLvl2 b).eval ((b.zs.getD s []).map zCode)
      == (outerLvl1 b).mats.getD s oneM) = true := by
    unfold zsK at hz
    simp only [List.all_eq_true] at hz ⊢
    intro s hs
    rw [beq_rows (canonB_eval _ _) ((lvl1Canon b).1 s), rowsOf_eval (lvl2Canon b), lvl2Mats,
      lvl2Invs, rowsOf_getD, lvl1Mats]
    exact hz s hs
  have e10 : ((outerLvl1 b).eval (b.neg.map zCode) == negM) = true := by
    rw [beq_rows (canonB_eval _ _) canonB_negM, rowsOf_eval (lvl1Canon b), lvl1Mats, lvl1Invs,
      rowsOf_negM]
    exact hn
  unfold outerBlockOK
  rw [lvl0Valid, e1, e2, m1, m2, e3, m4, m5, m6, e9, e10]
  rfl

theorem block2_eq : outerBlock 2 = B2 := by
  unfold outerBlock outerBlock2
  rw [if_pos rfl, owLines, parseBlock_eq owW 0 2 2 ch25030M_hdr.1]
  rfl

theorem block3_eq : outerBlock 3 = B3 := by
  unfold outerBlock outerBlock3
  rw [if_neg (by decide), owLines, parseBlock_eq owW 0 2 2 ch25030M_hdr.1]
  change (outerParseBlock owW.toArray 10).1 = B3
  rw [parseBlock_eq owW 10 2 2 ch25030M_hdr.2]
  rfl

end CertificateChecks.KernelSuz

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelSuz
open CFSG.EvenSporadicStandard.TwoSuz CFSG.Sporadic.Schreier.Tits
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore

theorem gens_comm {i : ℕ} (hi : i < 4) {ws : List (List Int)}
    (hl : ws.all (fun w => lettersK 2 w && cn (W3 w)) = true)
    (hc : ws.all (fun w => Nat.beq (pc (W3 w) (SuzTP i)) (pc (SuzTP i) (W3 w))) = true) :
    ws.all (fun w => outerCommutesT i w) = true := by
  obtain ⟨hT, cT, -⟩ := rep_facts hi
  simp only [List.all_eq_true] at hl hc ⊢
  intro w hw
  have h := hl w hw
  simp only [Bool.and_eq_true] at h
  have hA := fourArr h.1
  unfold foursWordArr at hA
  have cW : Cn (W3 w) := h.2
  unfold outerCommutesT
  rw [hA, hT, compA_u cW cT, compA_u cT cW, eqA_u (cpc cW cT) (cpc cT cW)]
  exact hc w hw

theorem check25030 : outerCheck = true := by
  have ok2 : outerBlockOK 2 B2 = true :=
    blockOK_of 2 B2 ch25030M_v2 ch25030M_misc.1 ch25030M_z2 ch25030M_neg.1
      (gens_comm (by decide) ch25030P_l.1 ch25030P_c2)
  have ok3 : outerBlockOK 3 B3 = true :=
    blockOK_of 3 B3 ch25030M_v3 ch25030M_misc.2 ch25030M_z3 ch25030M_neg.2
      (gens_comm (by decide) ch25030P_l.2 ch25030P_c3)
  unfold outerCheck
  rw [block2_eq, block3_eq, ok2, ok3]
  rfl

end CertificateChecks.KernelSpor.S26990

end
