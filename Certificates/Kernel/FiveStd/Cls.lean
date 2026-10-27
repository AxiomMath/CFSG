module

public import Certificates.Kernel.FiveStd.Data
public import Certificates.Kernel.FiveStd.ClsData
public import Certificates.Data.Kernel.FiveStdKOrb
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] noncomputable def clsF (k : Nat) : Bool :=
  clsOK G GI 2 (RP.getD k 0) (OR.getD k 0) (OM.getD k 0) (CB.getD k 0) (CM.getD k 0) (IV.getD k 0)

#kc_each CertificateChecks.FiveStd.ch5147c c (fun k => clsF k) 0 5

end CertificateChecks.FiveStd

end
