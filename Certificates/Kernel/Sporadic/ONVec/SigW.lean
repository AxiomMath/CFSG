module

public import Certificates.Kernel.Sporadic.ONVec.Data
public import CFSG.Certificates.Kernel.Spor.ONVKWSound

public section

namespace CertificateChecks.KernelSpor.ONVec

@[expose] noncomputable def sigSW (s : Nat) : Bool :=
  CFSG.KS.ONW.sigRangeW CertificateChecks.KernelSpor.ONS.K CertificateChecks.KernelSpor.ONV.K
    CertificateChecks.KernelSpor.ONS.LA (Nat.mul s (nat_lit 240)) (nat_lit 240)

theorem sigS_of_W (s : Nat) (h : sigSW s = true) : sigS s = true := CFSG.KS.ONW.sigRangeW_imp h

end CertificateChecks.KernelSpor.ONVec

end
