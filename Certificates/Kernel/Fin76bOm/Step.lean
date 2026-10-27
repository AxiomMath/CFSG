module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.YoshQ.Gen
public meta import Certificates.Kernel.Fin76bOm.J2
public meta import Certificates.Kernel.Fin76bOm.J3
public import Certificates.Kernel.Fin76bOm.J2
public import Certificates.Kernel.Fin76bOm.J3
public import Certificates.Kernel.YoshQ.Gen

public section

namespace CertificateChecks.KernelC24608

open CFSG.KC.Eval CFSG.Sporadic.Th.Native CFSG.EvenSporadicStandard.Fin76b
open CertificateChecks.KernelYoshQ

meta def omData (g : Nat) : Array Table × Nat × Nat :=
  if g == 0 then (j2OmTM.map fun a => a.map UInt32.ofNat, 32, 6)
  else (j3OmTM.map fun a => a.map UInt32.ofNat, 80, 7)

public meta def stepOm (vs : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let (ts, n, w) := omData (argN vs 0)
  let gens := ts.extract 0 (ts.size - 1)
  let tT := ts[ts.size - 1]!
  let W := (mulClosureS n n gens 2000).1
  let rts := wRoots n tT W
  let E := (mulClosureS n n rts 40).1
  if argN vs 1 == 0 then
    let bk := (W.findIdx? (betaOK n E)).getD W.size
    .ok (((recOf n w n 2000 gens).filter (·.1 != `IX)).push (`BK, .nat bk))
  else
    .ok ((recOf n w n 40 rts).filter (·.1 != `IX))

end CertificateChecks.KernelC24608

end
