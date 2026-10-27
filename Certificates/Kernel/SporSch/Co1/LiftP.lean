module

public import Certificates.Kernel.SporSch.Co1.Lift
public import CFSG.Certificates.Kernel.SporSch.Co1LiftProof
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.Co1Lift

open CFSG.KS.Raw CFSG.KS.SporSch.Lift CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
open CFSG.Sporadic.Co2Cert CertificateChecks.KernelSporSch.Co1Stab
open CertificateChecks.KernelSporSch.Co1Quot CertificateChecks.KernelSporSch.Co1Packed

theorem check_proved : liftCheck = true := by
  rw [spec_eq, z_eq, ← q0, ← q1, toArray_eq_of_bindListK a0, toArray_eq_of_bindListK a1,
    toArray_eq_of_bindListK bR, h0_eq, h1_eq, rows_of b0, rows_of b1]
  exact liftK_proved k

end CertificateChecks.KernelSporSch.Co1Lift

end
