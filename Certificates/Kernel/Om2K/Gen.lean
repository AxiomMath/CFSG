module

public import Certificates.Kernel.Om2K.Base
public import Certificates.Kernel.Om2K.ChecksG
public import Certificates.Kernel.OmegaEight.Aut
public import CFSG.Certificates.Kernel.SetOrbSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK)
open CFSG.EvenSmallLie.OmegaEight.Weyl (pairArr pairRepArr pArr)

theorem getElem!_getD (a : Array Nat) (i : Nat) : a[i]! = a.getD i 0 := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, Array.getD, dif_pos h]
    rfl
  · rw [getElem!_neg a i h, Array.getD, dif_neg h]
    rfl

theorem allLt_iff {n : Nat} {p : Nat → Bool} :
    CFSG.Monster.B.Co2.Native.allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold CFSG.Monster.B.Co2.Native.allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  exact ⟨fun h i hi => h ⟨i, hi⟩ (List.mem_finRange _), fun h i _ => h i i.2⟩

theorem ap_facts {j : Nat} (hj : j < 9) :
    canonK 360 9 (mask 9) (360 * 9) (CertificateChecks.KernelO8.AP.S j) = true ∧
      permOK 360 9 (mask 9) (360 * 9) (CertificateChecks.KernelO8.AP.S j)
        (pinv3 (CertificateChecks.KernelO8.AP.S j)) = true ∧
      canonK 360 9 (mask 9) (360 * 9) (pinv3 (CertificateChecks.KernelO8.AP.S j)) = true := by
  have h := allN_spec kG0 j hj
  obtain ⟨h1, h2⟩ := band h
  exact ⟨h1, band h2⟩

theorem conj360 {i : Nat} (hi : i < 8) :
    conjA 360 CFSG.EvenSmallLie.OmegaEight.genArrs[8]! CFSG.EvenSmallLie.OmegaEight.genArrs[i]! =
      unpack 360 9 (cj3 (CertificateChecks.KernelO8.AP.S 8) (CertificateChecks.KernelO8.AP.S i)) := by
  obtain ⟨a1, a2, a3⟩ := ap_facts (j := 8) (by norm_num)
  obtain ⟨b1, -, -⟩ := ap_facts (j := i) (by omega)
  rw [CertificateChecks.KernelO8.genAP.2 8 (by norm_num), CertificateChecks.KernelO8.genAP.2 i (by omega)]
  have a3' : canonK 360 9 (mask 9) (360 * 9)
      (pinvS 360 9 (mask 9) (CertificateChecks.KernelO8.AP.S 8)) = true := a3
  unfold conjA
  rw [invCand_unpack a2, compA_unpack b1 a3', compA_unpack a1 (canonK_pcomp b1 a3')]
  rfl

theorem yW_letters : yW.all wordOK = true := by decide

theorem gen_k : genCheck (reflTab ()) = true := by
  unfold genCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro w hw
    obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 hw
    have hlen : yW.length = 8 := by decide
    have hk8 : k < 8 := hlen ▸ hk
    have ew : yW.getD k [] = w := by rw [List.getD_eq_getElem _ _ hk, e]
    refine Bool.and_eq_true_iff.2 ⟨List.all_eq_true.1 yW_letters w hw, ?_⟩
    rw [← ew, (wA_eq _ (yW_lt k hk8)).1]
    exact validA_unpack (allN_spec kG3 k hk8)
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    obtain ⟨ew, cw⟩ := wA_eq _ (yW_lt i hi)
    rw [conj360 hi, ew]
    unfold eqA
    rw [allLt_iff]
    intro j hj
    have hr : pairRepArr[j]! < 240 := by
      rw [getElem!_getD]
      exact Nat.blt_eq.mp (allN_spec kG2 j hj)
    have h := Nat.eq_of_beq_eq_true (allN_spec (allN_spec kG1 i hi) j hj)
    have l1 : (res120 (unpack 360 9 (cj3 (CertificateChecks.KernelO8.AP.S 8)
        (CertificateChecks.KernelO8.AP.S i))))[j]! =
        pg 9 511 (cj3 (CertificateChecks.KernelO8.AP.S 8) (CertificateChecks.KernelO8.AP.S i)) j := by
      unfold res120
      rw [getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn, CFSG.KC.SetOrb.unpack_get (by omega)]
      rfl
    have l2 : (pArr (unpack 240 8 (wAK (yW.getD i []))))[j]! =
        pairArr.getD (pg 8 255 (wAK (yW.getD i [])) (pairRepArr.getD j 0)) 0 := by
      unfold pArr
      rw [getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn]
      simp only
      rw [CFSG.KC.SetOrb.unpack_get hr, getElem!_getD, getElem!_getD]
      rfl
    rw [l1, l2, h]
    exact beq_self_eq_true _

end CertificateChecks.KernelOm2

end
