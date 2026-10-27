module

public import Certificates.Kernel.SuzThree13637.HypData
public import Certificates.Data.Kernel.Spor.HypK
public import Certificates.Kernel.Sporadic.Suz.Chain2306
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CFSG.KD.SuzThree13637

open CFSG.KS.HypK CFSG.KS.PSearch CertificateChecks.KernelSpor

@[expose] noncomputable def ch13637S (r : Nat) : Bool :=
  searchOK 1782 11 SuzC.LR SuzC.TR SuzC.TRI SuzC.BP (nthL F.src r) (nthL F.Yl r) (nthL F.Yp r)

@[expose] noncomputable def ch13637B (r : Nat) : Bool :=
  bindOK 1782 11 SuzC.LR SuzC.TR SuzC.TRI SuzC.BP F.D (nthL F.gb r) (nthL F.ks r)
    (List.append (nthL F.Yl r) (nthL F.Yp r))

end CFSG.KD.SuzThree13637

#kc_each CFSG.KD.SuzThree13637.ch13637S 0 17

#kc_each CFSG.KD.SuzThree13637.ch13637B 0 17

namespace CFSG.KD.SuzThree13637

open CFSG.KS.HypK CFSG.KS.PSearch CertificateChecks.KernelSpor

theorem d_ok : dOK 1782 11 SuzC.LR SuzC.TRI SuzC.BP F.D = true := by quickRfl

theorem n_ok : nOK 1782 11 SuzC.LR SuzC.TR SuzC.TRI SuzC.BP F.D F.nb F.M = true := by quickRfl

theorem fr_ok : frOK F.hm F.M F.fr = true := by quickRfl

theorem orth_ok : CFSG.KC.Enum.allN 17 (fun r => orthOK (nthN F.hm r) (nthL F.ks r)) = true := by
  quickRfl

end CFSG.KD.SuzThree13637

end
