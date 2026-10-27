module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.E6TableT

public section

namespace CertificateChecks.KernelE6TT.GenRow

open CFSG.KC.Eval Certificates.Data.E6TableT

meta def packV (x : Vec) : Except String Nat :=
  x.foldr (fun c acc => do
    let a ← acc
    unless -3 ≤ c && c ≤ 4 do throw s!"coordinate {c} out of range"
    return (a <<< 3) ||| (c + 3).toNat) (pure 0)

public meta def rootRecs (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let R := roots ()
  unless R.length == 72 do throw s!"{R.length} roots"
  let mut V := 0
  for x in R.reverse do
    V := (V <<< 18) ||| (← packV x)
  return #[(`V, .nat V)]

end CertificateChecks.KernelE6TT.GenRow

end
