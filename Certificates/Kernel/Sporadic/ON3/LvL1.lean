module

public import Certificates.Kernel.Sporadic.ON3.Defs
public import CFSG.Certificates.Kernel.Spor.CBFwd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS.CB CFSG.KS.CH

@[expose] noncomputable def ptL1F (s : Nat) : Bool :=
  cbPtRangeF 245520 (lMr 1) (lLEN 1) (stepX lF lFI (lIDX 1) (lLEN 1)) (lPTS 1) (lPOS 1) (lPAR 1)
    (lLAB 1) (Nat.mul s 16) 16

end CertificateChecks.KernelSpor.ON3

#kon_slices CertificateChecks.KernelSpor.ON3.ptL1F 0 21

end
