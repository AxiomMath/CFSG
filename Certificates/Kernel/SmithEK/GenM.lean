module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.SmithEModel

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.SmithE CFSG.F4.Native

public meta def mStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "mStep: expected no arguments"
  let L := (uPts ()).toList
  let bits (m : Nat) : Nat :=
    L.foldr (fun p acc => (if m.testBit p then 1 else 0) + 2 * acc) 0
  return #[(`P, .list ((List.range 891).toArray.map fun i => .nat (bits (wMask i))))]

end CertificateChecks.KernelSmithEK
