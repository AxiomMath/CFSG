module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.Kernel.SmithEKS
public meta import Certificates.Data.CFSGNative.F4.Unitary

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval

public meta def packStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "packStep: expected no arguments"
  let cols := (CFSG.F4.Native.uPts ()).toList.map fun p => CFSG.SmithE.K.tvW CFSG.SmithE.K.cTabQ p
  let C := (List.range 20).map fun m =>
    cols.zipIdx.foldl (fun acc ck => acc ||| (ck.1.getD m 0 <<< (20 * ck.2))) 0
  return #[(`C, .list (C.toArray.map .nat))]

end CertificateChecks.KernelSmithEK
