
module

public import Certificates.Kernel.Sporadic.ON3.Defs
public import CFSG.Certificates.Kernel.Spor.CBFwd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS.CB CFSG.KS.CH

@[expose] noncomputable def ptM1F (s : Nat) : Bool :=
  cbPtRangeF 245520 (mMr 1) (mLEN 1) (stepX mF mFI (mIDX 1) (mLEN 1)) (mPTS 1) (mPOS 1) (mPAR 1)
    (mLAB 1) (Nat.mul s 16) 16

end CertificateChecks.KernelSpor.ON3

#kon_slices CertificateChecks.KernelSpor.ON3.ptM1F 0 42

end
