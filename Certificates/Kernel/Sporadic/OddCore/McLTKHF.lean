module

public import Certificates.Data.Kernel.Spor.MulHF
public import Certificates.Kernel.Sporadic.OddCore.McLTC

public section

namespace CertificateChecks.KernelSpor.McLTK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.MulH

@[expose] noncomputable def hSlF (s : Nat) : Bool :=
  slK McLTC.cnt (hsortPtKF 275 9 (mask 9) McLTC.cnt McLTC.T McLTC.HS McLTC.HSI) (Nat.mul 1100 s)
    1100

end CertificateChecks.KernelSpor.McLTK

end
