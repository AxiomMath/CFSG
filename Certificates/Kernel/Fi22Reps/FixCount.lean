module

public import Certificates.Kernel.Fi22Reps.Each
public import Certificates.Data.Kernel.Fi22Reps.FixCount

public section

namespace CertificateChecks.KernelFi22Reps

open CFSG.KC.Fi22Reps

theorem ch10133fix :
    fixCntK (xT 0) = 0 ∧ fixCntK (xT 1) = 27 ∧ fixCntK (xT 2) = 36 ∧ fixCntK (xT 3) = 126 := by
  decide +kernel

end CertificateChecks.KernelFi22Reps
