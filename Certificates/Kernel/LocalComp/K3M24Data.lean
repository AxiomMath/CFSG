module

public import Certificates.Kernel.LocalComp.K3Gen
public import CFSG.Certificates.Kernel.K3Defs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3MathieuData
meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3MathieuData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.K3.M24T CFSG.EvenSmallLie.Child3.SelK3.m24K3Prog
#lc_k3 CertificateChecks.KernelLC.K3.M24 CFSG.EvenSmallLie.Child3.SelK3.m24K3

namespace CertificateChecks.KernelLC.K3.M24

open CFSG.KC.K3

@[expose] noncomputable def fS (t : Nat) : Bool := K.stepK t
@[expose] noncomputable def fF (r : Nat) : Bool := K.finK r
@[expose] noncomputable def fE (k : Nat) : Bool := K.eK k
@[expose] noncomputable def fC (p : Nat) : Bool := K.cK p
@[expose] noncomputable def fM (k : Nat) : Bool := K.memK k
@[expose] noncomputable def fW (j : Nat) : Bool := K.witK j

end CertificateChecks.KernelLC.K3.M24

end
