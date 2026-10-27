module

public import Certificates.Kernel.Sporadic.OddCore.HL
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.Misc.HexAt

@[expose] noncomputable def dEF1 (k : Nat) : Bool :=
  penumSlK 105 7 (mask 7) (105 * 7) false HDE.G HDE.GI 5 HDE.cnt
    HDE.T HDE.PL HDE.POS HDE.SRT HDE.SRI (450 * k) 450

#kc_each_unfold dEF1 23 45 as CertificateChecks.KernelSpor.HeL.dE

end CertificateChecks.KernelSpor.HeL

end
