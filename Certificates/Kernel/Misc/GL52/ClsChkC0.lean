module

public import Certificates.Kernel.Misc.GL52.ClsTab
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.GL52K

open CFSG.KC.Misc.GLM CFSG.KC.Ord

theorem chunk0_a : ∀ c < 4,
    Nat.beq (unitCntR (D.basR 0) (0 + c * 8192) 8192) (D.parts0.getD c 0) = true := by
  intro c hc
  interval_cases c <;> quickRfl

theorem chunk0_b : ∀ c < 4,
    Nat.beq (unitCntR (D.basR 0) (0 + (c + 4) * 8192) 8192) (D.parts0.getD (c + 4) 0) = true := by
  intro c hc
  interval_cases c <;> quickRfl

theorem chunk0_c : ∀ c < 4,
    Nat.beq (unitCntR (D.basR 0) (0 + (c + 8) * 8192) 8192) (D.parts0.getD (c + 8) 0) = true := by
  intro c hc
  interval_cases c <;> quickRfl

theorem chunk0_d : ∀ c < 4,
    Nat.beq (unitCntR (D.basR 0) (0 + (c + 12) * 8192) 8192) (D.parts0.getD (c + 12) 0) = true := by
  intro c hc
  interval_cases c <;> quickRfl

end CertificateChecks.KernelMisc.GL52K

end
