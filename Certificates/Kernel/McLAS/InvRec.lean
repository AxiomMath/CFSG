module

public import Certificates.Kernel.Sporadic.OddCore.MNR1
public import Certificates.Data.Kernel.McLAS.Three

public section

namespace CertificateChecks.KernelMcLAS

open CFSG.KS.MulH CFSG.KS.McLAS

@[expose] noncomputable def ipSl (s : Nat) : Bool :=
  slK CertificateChecks.KernelSpor.MN.R1.cnt
    (fun i => ord6K (pcK CertificateChecks.KernelSpor.MN.R1.R (CertificateChecks.KernelSpor.MN.R1.T i)))
    (Nat.mul s (nat_lit 200)) (nat_lit 200)

end CertificateChecks.KernelMcLAS

end
