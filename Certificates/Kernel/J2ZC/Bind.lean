module

public import Certificates.Kernel.J2ZC.Data
public import Certificates.Kernel.Sporadic.OddCore.J2PChain

public section

namespace CertificateChecks.J2ZCK

open CFSG.KD.J2ZC CertificateChecks.KernelSpor

theorem a_eq : Nat.beq A (J2P.S 0) = true := by decide +kernel
theorem ai_eq : Nat.beq AI (J2P.SI 0) = true := by decide +kernel
theorem b_eq : Nat.beq B (J2P.S 1) = true := by decide +kernel
theorem bi_eq : Nat.beq BI (J2P.SI 1) = true := by decide +kernel

end CertificateChecks.J2ZCK

end
