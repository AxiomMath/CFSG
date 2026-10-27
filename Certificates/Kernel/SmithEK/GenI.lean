module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.CFSGNative.F4.Unitary
public meta import Certificates.Data.Kernel.SmithEKI

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.F4.Native

public meta def basStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "basStep: expected no arguments"
  return #[(`L, .list ((uPts ()).map fun p =>
    .list ((CFSG.SmithE.K.basL (CFSG.SmithE.K.tvW CFSG.SmithE.K.cTabQ p)).toArray.map .nat)))]

end CertificateChecks.KernelSmithEK
