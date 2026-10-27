module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.CFSGNative.F4.Unitary

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.F4.Native

public meta def ptsStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "ptsStep: expected no arguments"
  return #[(`L, .list ((uPts ()).map .nat))]

end CertificateChecks.KernelSmithEK
