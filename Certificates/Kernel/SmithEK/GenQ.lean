module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LargeExtraspecial.S14SMKModCheck
public import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.SmithE

meta def qzRecs (gs : Array (Nat × Nat)) (vs : Array Nat) : Val :=
  .list ((List.range gs.size).toArray.map fun s =>
    .nat (vs[s]! + 2 ^ 20 * (gs[s]!.1 + 1024 * gs[s]!.2)))

public meta def qzStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let some (Val.nat i) := args[0]? | throw "qzStep: expected the plane"
  let qv := qaVecs i
  let cv := cvVecs i
  return #[(`QG, qzRecs (qaGens i) qv), (`QU, .list ((vecDual qv).map .nat)),
    (`CG, qzRecs (cvGens i) cv), (`CU, .list ((vecDual cv).map .nat))]

end CertificateChecks.KernelSmithEK
