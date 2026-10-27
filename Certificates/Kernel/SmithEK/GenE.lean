module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.SMod20BasicC8
public import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval

public meta def c8ColStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let some (Val.list cols) := args[0]? | throw "c8ColStep: expected the column list"
  let pick (r : Nat) : Except String Val :=
    match cols[r]? with
    | some v => pure v
    | none => throw "c8ColStep: point out of range"
  let q ← CFSG.SmithE.c8Pts.toList.mapM pick
  let s ← CFSG.SmithE.rigS.mapM pick
  return #[(`Q, .list q.toArray), (`S, .list s.toArray)]

end CertificateChecks.KernelSmithEK
