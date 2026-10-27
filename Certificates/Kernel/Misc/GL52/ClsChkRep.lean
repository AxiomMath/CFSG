module

public import Certificates.Kernel.Misc.GL52.ClsTab
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.GL52K

open CFSG.KC.Misc.GLM CFSG.KC.Ord

theorem repOK_lo : ∀ i < 13, repOK i = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem repOK_hi : ∀ i < 13, repOK (i + 13) = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem basR_lo : ∀ i < 13, basOK (pR i) (D.basR i) = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem basR_hi : ∀ i < 13, basOK (pR (i + 13)) (D.basR (i + 13)) = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem cntR_ok : ∀ i < 25,
    Nat.beq (unitCntK (D.basR (i + 1))) (D.repN.getD (i + 1) 0) = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem idV_ok : Nat.beq (invK idK) D.idV = true := by
  quickRfl

theorem basZ_ok : basOK pZ D.bZ = true := by
  quickRfl

theorem cntZ_ok : Nat.beq (unitCntK D.bZ) D.nZ = true := by
  quickRfl

end CertificateChecks.KernelMisc.GL52K

end
