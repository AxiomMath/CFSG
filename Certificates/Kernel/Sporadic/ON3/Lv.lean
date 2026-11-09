
module

public import Certificates.Kernel.Sporadic.ON3.Defs
public import CFSG.Certificates.Kernel.Spor.CBFwd
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS.CB CFSG.KS.CH

theorem heads_ok : headsOK = true := by quickRfl

theorem sifts_ok : siftsOK = true := by quickRfl

@[expose] noncomputable def ptT0F (s : Nat) : Bool :=
  cbPtRangeF 245520 (tMr 0) (tLEN 0) (stepX tF tFI (tIDX 0) (tLEN 0)) (tPTS 0) (tPOS 0) (tPAR 0)
    (tLAB 0) (Nat.mul s 16) 16

@[expose] noncomputable def ptT1F (s : Nat) : Bool :=
  cbPtRangeF 245520 (tMr 1) (tLEN 1) (stepX tF tFI (tIDX 1) (tLEN 1)) (tPTS 1) (tPOS 1) (tPAR 1)
    (tLAB 1) (Nat.mul s 16) 16

@[expose] noncomputable def ptM0F (s : Nat) : Bool :=
  cbPtRangeF 245520 (mMr 0) (mLEN 0) (stepX mF mFI (mIDX 0) (mLEN 0)) (mPTS 0) (mPOS 0) (mPAR 0)
    (mLAB 0) (Nat.mul s 16) 16

@[expose] noncomputable def ptL0F (s : Nat) : Bool :=
  cbPtRangeF 245520 (lMr 0) (lLEN 0) (stepX lF lFI (lIDX 0) (lLEN 0)) (lPTS 0) (lPOS 0) (lPAR 0)
    (lLAB 0) (Nat.mul s 16) 16

end CertificateChecks.KernelSpor.ON3

#kon_slices CertificateChecks.KernelSpor.ON3.posS 0 72
#kon_slices CertificateChecks.KernelSpor.ON3.ptT0F 0 8
#kon_slices CertificateChecks.KernelSpor.ON3.ptT1F 0 1
#kon_slices CertificateChecks.KernelSpor.ON3.ptT2 0 1
#kon_slices CertificateChecks.KernelSpor.ON3.ptM0F 0 15
#kon_slices CertificateChecks.KernelSpor.ON3.ptM2 0 1
#kon_slices CertificateChecks.KernelSpor.ON3.ptL0F 0 15
#kon_slices CertificateChecks.KernelSpor.ON3.ptL2 0 1

end
