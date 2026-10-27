module

public import Certificates.Kernel.PlusQuandle.Data
public import CFSG.Certificates.Kernel.PlusQuandleSound

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPlusQ

open CFSG.OddTranspositions.PartThree CFSG.KD.PlusQuandle

theorem noncomm_ok : plusQuandleNoncommCheck () = true := by decide +kernel

theorem rows_ok : rowsOK R = true := by decide +kernel

theorem deriv_ok : derivOK D = true := by decide +kernel

theorem prim_ok : primS R = true := by decide +kernel

theorem ch1383002p_0 : perpOK R D 0 5 = true := by decide +kernel
theorem ch1383002p_1 : perpOK R D 5 10 = true := by decide +kernel
theorem ch1383002p_2 : perpOK R D 10 15 = true := by decide +kernel
theorem ch1383002p_3 : perpOK R D 15 20 = true := by decide +kernel
theorem ch1383002p_4 : perpOK R D 20 25 = true := by decide +kernel
theorem ch1383002p_5 : perpOK R D 25 30 = true := by decide +kernel
theorem ch1383002p_6 : perpOK R D 30 35 = true := by decide +kernel
theorem ch1383002p_7 : perpOK R D 35 40 = true := by decide +kernel
theorem ch1383002p_8 : perpOK R D 40 45 = true := by decide +kernel
theorem ch1383002p_9 : perpOK R D 45 50 = true := by decide +kernel
theorem ch1383002p_10 : perpOK R D 50 55 = true := by decide +kernel
theorem ch1383002p_11 : perpOK R D 55 60 = true := by decide +kernel

theorem perp_all {a : ℕ} (ha : a < 60) : perpA R D a = true := by
  have h : ∀ k, k < 12 → ∀ a, 5 * k ≤ a → a < 5 * k + 5 → perpA R D a = true := by
    intro k hk a h1 h2
    have hc : perpOK R D (5 * k) (5 * k + 5) = true := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
          k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ch1383002p_0
      · exact ch1383002p_1
      · exact ch1383002p_2
      · exact ch1383002p_3
      · exact ch1383002p_4
      · exact ch1383002p_5
      · exact ch1383002p_6
      · exact ch1383002p_7
      · exact ch1383002p_8
      · exact ch1383002p_9
      · exact ch1383002p_10
      · exact ch1383002p_11
    exact CFSG.KC.PlusQuandle.perpOK_spec hc h1 h2
  exact h (a / 5) (by omega) a (by omega) (by omega)

end CertificateChecks.KernelPlusQ
