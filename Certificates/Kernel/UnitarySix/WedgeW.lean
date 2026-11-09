module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDWedgeCert
public import Certificates.Data.Kernel.U6.WedgeRN
import CFSG.Certificates.Kernel.U6WedgeProved
public import CFSG.Certificates.Kernel.U6LinSound
public import Certificates.Data.Kernel.U6.WedgeK
public import Certificates.Data.Kernel.U6.WedgeGap
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6

open CFSG.KC.U6F2 CFSG.KLie.CT CFSG.KC.Loop
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (toMat)
open CFSG.EvenSmallLie.UnitarySix.YamadaD (wedgeGensN wedgeGensW wedgeMatN wedgeMatW wedgeR
  wedgeCheckWith wedgeCheckNW wedgeCheckWW wedgeQN wedgeQW)

@[expose] noncomputable def wedgeGNP : List ℕ :=
  [11551768297464988161, 10407853992129724929, 9241430501863195137, 2310487621240948740,
    9241395249175069185]

@[expose] noncomputable def wedgeGWP : List ℕ := [54321, 46369, 5224]

theorem wedgeRows_all :
    entAllK (fun ρ r => Nat.beq (wRowK 8 5 wedgeGNP ρ) r) wedgeRNL 0 = true := by
  quickRfl

theorem wedgeRNL_length : wedgeRNL.length = 3072 := by decide +kernel

theorem wedgeRN : (wedgeR wedgeMatN).toList = wedgeRNL := by
  change (wedgeR fun g : Fin 5 => toMat 8 8 (wedgeGensN.getD g #[])).toList = _
  rw [wedgeR_toList_proved (fun g => wedgeGensN.getD g #[]) (GP := wedgeGNP) (by decide +kernel)]
  apply List.ext_getElem (by rw [wedgeRNL_length]; simp [wedgeRK])
  intro ρ h1 h2
  have h : Nat.beq (wRowK 8 5 wedgeGNP (0 + ρ)) wedgeRNL[ρ] = true :=
    entAllK_spec _ wedgeRNL 0 wedgeRows_all ρ h2
  rw [Nat.zero_add] at h
  simp only [wedgeRK, List.getElem_map, List.getElem_range]
  exact Nat.eq_of_beq_eq_true h

theorem wedgeGap_0 :
    wgAllK wedgeRNL (wgDropL (64 * 0) wedgeQN.toList) (getLD [] wgS 0) (64 * 0) = true := by
  quickRfl
theorem wedgeGap_1 :
    wgAllK wedgeRNL (wgDropL (64 * 1) wedgeQN.toList) (getLD [] wgS 1) (64 * 1) = true := by
  quickRfl
theorem wedgeGap_2 :
    wgAllK wedgeRNL (wgDropL (64 * 2) wedgeQN.toList) (getLD [] wgS 2) (64 * 2) = true := by
  quickRfl
theorem wedgeGap_3 :
    wgAllK wedgeRNL (wgDropL (64 * 3) wedgeQN.toList) (getLD [] wgS 3) (64 * 3) = true := by
  quickRfl
theorem wedgeGap_4 :
    wgAllK wedgeRNL (wgDropL (64 * 4) wedgeQN.toList) (getLD [] wgS 4) (64 * 4) = true := by
  quickRfl
theorem wedgeGap_5 :
    wgAllK wedgeRNL (wgDropL (64 * 5) wedgeQN.toList) (getLD [] wgS 5) (64 * 5) = true := by
  quickRfl
theorem wedgeGap_6 :
    wgAllK wedgeRNL (wgDropL (64 * 6) wedgeQN.toList) (getLD [] wgS 6) (64 * 6) = true := by
  quickRfl
theorem wedgeGap_7 :
    wgAllK wedgeRNL (wgDropL (64 * 7) wedgeQN.toList) (getLD [] wgS 7) (64 * 7) = true := by
  quickRfl

theorem wgS_len : ∀ c < 8, (getLD [] wgS c).length = 64 := by decide +kernel

theorem wedgeCheckNW_true : wedgeCheckNW = true := by
  change wedgeCheckWith 8 5 wedgeMatN wedgeQN = true
  refine bIsId_bmul_of_rows_proved wedgeRN wedgeRNL_length (rowMulZ_of_slices (m := 8) ?_ wgS_len)
  intro c hc
  interval_cases c
  exacts [wedgeGap_0, wedgeGap_1, wedgeGap_2, wedgeGap_3, wedgeGap_4, wedgeGap_5, wedgeGap_6,
    wedgeGap_7]

theorem wedgeCheckWW_true : wedgeCheckWW = true := by
  change wedgeCheckWith 4 3 wedgeMatW wedgeQW = true
  have hR : (wedgeR wedgeMatW).toList = wedgeRK 4 3 wedgeGWP :=
    wedgeR_toList_proved (fun g => wedgeGensW.getD g #[]) (by decide +kernel)
  exact bIsId_bmul_of_idRowsK_proved hR (by decide +kernel) (by decide +kernel)

end CertificateChecks.KernelU6
