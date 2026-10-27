module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.E6TableT

public section

namespace CertificateChecks.KernelE6TT.Gen

open CFSG.KC.Eval Certificates.Data.E6TableT

meta def gramRow (R : List Vec) (x : Vec) : Nat :=
  R.foldr (fun y acc => (acc <<< 3) ||| (iform x y % 8).toNat) 0

meta def flagBits (x : Vec) : Nat :=
  reps.foldr (fun v acc => (acc <<< 6) |||
    (List.range 6).foldr (fun l a => (a <<< 1) |||
      (if (dot x v - 2 * v.getD l 0) % 3 == 0 then 1 else 0)) 0) 0

meta def packIdx (js : List Nat) : Nat := js.foldr (fun j acc => (acc <<< 7) ||| (j + 1)) 0

meta def slots (w : Nat) (xs : List Nat) : Nat := xs.foldr (fun s acc => (acc <<< w) ||| s) 0

public meta def recs (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let R := roots ()
  unless R.length == 72 do throw s!"{R.length} roots"
  let G := R.map (gramRow R)
  let F := R.map flagBits
  let lane (i j : Nat) : Nat := ((G.getD i 0) >>> (3 * j)) % 8
  let fl (j b : Nat) : Bool := ((F.getD j 0) >>> b) % 2 == 1
  let idx := List.range 72
  let mut out : Array (Lean.Name × Val) := #[(`GR, .nat (slots 216 G)), (`FL, .nat (slots 30 F))]
  for k in [0:5] do
    out := out.push (Lean.Name.mkSimple s!"L{k}", .nat (packIdx (idx.filter fun j => fl j (6 * k))))
    for l in [1:6] do
      let N := slots 140 (idx.map fun i =>
        packIdx (idx.filter fun j => lane i j == 7 && fl j (6 * k + l)))
      out := out.push (Lean.Name.mkSimple s!"N{k}{l}", .nat N)
  return out

end CertificateChecks.KernelE6TT.Gen

end
