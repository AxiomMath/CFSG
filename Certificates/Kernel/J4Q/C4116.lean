module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZK
public import Certificates.Kernel.J4Q.QTBase
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.J4.QT2LocX0Native

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

open Certificates in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 in
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 in
theorem c4116 : (∀ c < 2048, wfRows (etaE c) = true) :=
  fun c _ => wf_bool (eta_enc c).1

end CertificateChecks.KernelJ4Q

end
