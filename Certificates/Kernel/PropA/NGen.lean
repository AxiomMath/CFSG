module

public meta import Certificates.Kernel.PropA.FactGen
public import Certificates.Kernel.PropA.FactGen

public section

namespace CertificateChecks.KernelPropA.Gen

open CFSG.PSL3Four.Native CertificateChecks.KernelPropA

meta def nW (b : Bool) : Array (Array Nat) :=
  let t := (gensK b)[3]!
  #[idT, t, comp 28 t rx, rx]

meta def nPair (b : Bool) (gs : Array (Array Nat)) (g : Array Nat) : Array Nat := Id.run do
  let ws := nW b
  for k in [0:ws.size] do
    match tJ.findIdx? (· == comp 28 (invTab 28 ws[k]!) g) with
    | some j => return #[k, j]
    | none => pure ()
  for c in [0:gs.size] do
    let z := comp 28 (comp 28 (comp 28 (comp 28 (invTab 28 g) (invTab 28 rx)) gs[c]!) g)
      (invTab 28 gs[c]!)
    match tJ.findIdx? (· == z) with
    | some j => return #[ws.size + c, j]
    | none => pure ()
  return #[255, 255]

meta def nW1 : Array (Array Nat) := nW false
meta def nW2 : Array (Array Nat) := nW true
meta def nE1 : Array (Array Nat) := (enumT false gCKX1 giCKX1 idT 960).map (nPair false gCKX1)
meta def nE2 : Array (Array Nat) := (enumT false gCKX2 giCKX2 idT 960).map (nPair true gCKX2)

end CertificateChecks.KernelPropA.Gen

end
