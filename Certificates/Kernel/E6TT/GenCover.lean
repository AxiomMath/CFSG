module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.E6TableT
public import Certificates.Data.E6TableT

public section

namespace CertificateChecks.KernelE6TT.GenCover

open CFSG.KC.Eval Certificates.Data.E6TableT

meta def encV (v : Vec) : Nat := v.foldr (fun x acc => x.toNat + 3 * acc) 0

meta def decV (c : Nat) : Vec := (List.range 6).map fun i => Int.ofNat (c / 3 ^ i % 3)

public meta def coverRecs (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let mut seen : Array Bool := Array.replicate 729 false
  let mut out : Array Nat := #[]
  for (v, k) in reps.zipIdx do
    let c := encV v
    if seen[c]! then throw s!"representative {k} already reached"
    seen := seen.set! c true
    out := out.push (c + (7 + k) * 2 ^ 20)
    let mut frontier := #[c]
    while !frontier.isEmpty do
      let mut next := #[]
      for p in frontier do
        for j in [0:7] do
          let d := encV (genAct j (decV p))
          if !seen[d]! then
            seen := seen.set! d true
            out := out.push (d + p * 2 ^ 10 + j * 2 ^ 20)
            next := next.push d
      frontier := next
  unless out.size == 728 do throw s!"{out.size} entries"
  return #[(`CT, .list (out.map .nat))]

end CertificateChecks.KernelE6TT.GenCover

end
