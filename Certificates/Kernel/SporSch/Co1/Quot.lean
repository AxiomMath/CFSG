module

public import Certificates.Kernel.SporSch.Co1.Stab
public import CFSG.Sporadic.Schreier.Co1QuotCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1QuotData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Quot

meta def QA0 : Array Nat := CFSG.Sporadic.Co1Schreier.Data.quotAct0.toArray

meta def QA1 : Array Nat := CFSG.Sporadic.Co1Schreier.Data.quotAct1.toArray

end CertificateChecks.KernelSporSch.Co1Quot

#ks_perm CertificateChecks.KernelSporSch.Co1Quot.Q0 12 CertificateChecks.KernelSporSch.Co1Quot.QA0

#ks_perm CertificateChecks.KernelSporSch.Co1Quot.Q1 12 CertificateChecks.KernelSporSch.Co1Quot.QA1

namespace CertificateChecks.KernelSporSch.Co1Quot

open CFSG.KS.Raw CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co2Cert
open CertificateChecks.KernelSporSch.Co1Stab

theorem a0 : bindListK 2300 12 Q0 Data.quotAct0 = true := by quickRfl
theorem a1 : bindListK 2300 12 Q1 Data.quotAct1 = true := by quickRfl
theorem g0 : bindListK 2300 12 Q0 co2G0 = true := by quickRfl
theorem g1 : bindListK 2300 12 Q1 co2G1 = true := by quickRfl

theorem orig : co2OrigArrs = #[co2G0.toArray, co2G1.toArray] := by
  unfold co2OrigArrs co2Rec
  rfl

theorem q0 : Data.quotAct0.toArray = co2OrigArrs[0]! := by
  rw [orig, toArray_eq_of_bindListK a0, ← toArray_eq_of_bindListK g0]
  rfl

theorem q1 : Data.quotAct1.toArray = co2OrigArrs[1]! := by
  rw [orig, toArray_eq_of_bindListK a1, ← toArray_eq_of_bindListK g1]
  rfl

theorem check : quotCheck = true := by
  unfold quotCheck quotCheckOf
  rw [← q0, ← q1, h0_eq, h1_eq]
  simp only [beq_self_eq_true, Bool.and_self]

end CertificateChecks.KernelSporSch.Co1Quot

end
