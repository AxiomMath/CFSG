module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.Kernel.SmithEKS
public meta import Certificates.Data.CFSGNative.F4.Unitary

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval

public meta def cwStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "cwStep: expected no arguments"
  let E := (CFSG.F4.Native.uPts ()).map fun p =>
    let c := CFSG.SmithE.K.tvW CFSG.SmithE.K.cTabQ p
    ((List.range 2048).find? fun e => CFSG.SmithE.isWt (CFSG.SmithE.K.applyL c e ^^^ e)).getD 2048
  return #[(`E, .list (E.map .nat))]

end CertificateChecks.KernelSmithEK
