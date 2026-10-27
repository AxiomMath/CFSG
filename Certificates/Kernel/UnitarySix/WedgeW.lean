module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDWedgeCert
public import Certificates.Data.Kernel.U6.WedgeRN
import CFSG.Certificates.Kernel.U6WedgeProved
public import CFSG.Certificates.Kernel.U6LinSound
public import Certificates.Data.Kernel.U6.WedgeK

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

@[expose] noncomputable def wedgeRows (s : ℕ) : Bool :=
  (List.range' (192 * s) 192).all fun ρ => Nat.beq (wRowK 8 5 wedgeGNP ρ) (getLD 0 wedgeRNL ρ)

theorem wedgeRows_0 : wedgeRows 0 = true := by decide +kernel
theorem wedgeRows_1 : wedgeRows 1 = true := by decide +kernel
theorem wedgeRows_2 : wedgeRows 2 = true := by decide +kernel
theorem wedgeRows_3 : wedgeRows 3 = true := by decide +kernel
theorem wedgeRows_4 : wedgeRows 4 = true := by decide +kernel
theorem wedgeRows_5 : wedgeRows 5 = true := by decide +kernel
theorem wedgeRows_6 : wedgeRows 6 = true := by decide +kernel
theorem wedgeRows_7 : wedgeRows 7 = true := by decide +kernel
theorem wedgeRows_8 : wedgeRows 8 = true := by decide +kernel
theorem wedgeRows_9 : wedgeRows 9 = true := by decide +kernel
theorem wedgeRows_10 : wedgeRows 10 = true := by decide +kernel
theorem wedgeRows_11 : wedgeRows 11 = true := by decide +kernel
theorem wedgeRows_12 : wedgeRows 12 = true := by decide +kernel
theorem wedgeRows_13 : wedgeRows 13 = true := by decide +kernel
theorem wedgeRows_14 : wedgeRows 14 = true := by decide +kernel
theorem wedgeRows_15 : wedgeRows 15 = true := by decide +kernel

theorem wedgeRNL_length : wedgeRNL.length = 3072 := by decide +kernel

theorem wedgeRN : (wedgeR wedgeMatN).toList = wedgeRNL := by
  change (wedgeR fun g : Fin 5 => toMat 8 8 (wedgeGensN.getD g #[])).toList = _
  rw [wedgeR_toList_proved (fun g => wedgeGensN.getD g #[]) (GP := wedgeGNP) (by decide +kernel)]
  have hrows : ∀ s < 16, wedgeRows s = true := by
    intro s hs
    interval_cases s
    exacts [wedgeRows_0, wedgeRows_1, wedgeRows_2, wedgeRows_3, wedgeRows_4, wedgeRows_5,
      wedgeRows_6, wedgeRows_7, wedgeRows_8, wedgeRows_9, wedgeRows_10, wedgeRows_11,
      wedgeRows_12, wedgeRows_13, wedgeRows_14, wedgeRows_15]
  apply List.ext_getElem (by rw [wedgeRNL_length]; simp [wedgeRK])
  intro ρ h1 h2
  have hρ : ρ < 3072 := by simpa [wedgeRK] using h1
  have h := List.all_eq_true.mp (hrows (ρ / 192) (by omega)) ρ
    (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  simp only [wedgeRK, List.getElem_map, List.getElem_range]
  rw [Nat.eq_of_beq_eq_true h, getLD_eq_getD, List.getD_eq_getElem _ _ h2]

theorem wedgeBlock_0 : blockRowsK 512 0 wedgeQN.toList wedgeRNL = true := by decide +kernel
theorem wedgeBlock_1 : blockRowsK 512 1 wedgeQN.toList wedgeRNL = true := by decide +kernel
theorem wedgeBlock_2 : blockRowsK 512 2 wedgeQN.toList wedgeRNL = true := by decide +kernel
theorem wedgeBlock_3 : blockRowsK 512 3 wedgeQN.toList wedgeRNL = true := by decide +kernel
theorem wedgeBlock_4 : blockRowsK 512 4 wedgeQN.toList wedgeRNL = true := by decide +kernel
theorem wedgeBlock_5 : blockRowsK 512 5 wedgeQN.toList wedgeRNL = true := by decide +kernel
theorem wedgeBlock_6 : blockRowsK 512 6 wedgeQN.toList wedgeRNL = true := by decide +kernel
theorem wedgeBlock_7 : blockRowsK 512 7 wedgeQN.toList wedgeRNL = true := by decide +kernel

theorem wedgeCheckNW_true : wedgeCheckNW = true := by
  change wedgeCheckWith 8 5 wedgeMatN wedgeQN = true
  refine bIsId_bmul_of_blocks_proved (k := 8) wedgeRN wedgeRNL_length fun c hc => ?_
  interval_cases c
  exacts [wedgeBlock_0, wedgeBlock_1, wedgeBlock_2, wedgeBlock_3, wedgeBlock_4, wedgeBlock_5,
    wedgeBlock_6, wedgeBlock_7]

theorem wedgeCheckWW_true : wedgeCheckWW = true := by
  change wedgeCheckWith 4 3 wedgeMatW wedgeQW = true
  have hR : (wedgeR wedgeMatW).toList = wedgeRK 4 3 wedgeGWP :=
    wedgeR_toList_proved (fun g => wedgeGensW.getD g #[]) (by decide +kernel)
  exact bIsId_bmul_of_idRowsK_proved hR (by decide +kernel) (by decide +kernel)

end CertificateChecks.KernelU6
