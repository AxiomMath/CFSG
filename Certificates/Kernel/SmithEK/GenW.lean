module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.SmithEModel

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.SmithE

public meta def wStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "wStep: expected no arguments"
  return #[(`W, .list ((List.range 891).toArray.map fun i => .nat (wt i))),
    (`M, .list ((List.range 891).toArray.map fun i => .nat (wMask i)))]

end CertificateChecks.KernelSmithEK
