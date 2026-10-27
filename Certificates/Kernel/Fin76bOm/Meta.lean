module

public section

namespace CertificateChecks.KernelC24608

meta def orbitM (gs : Array (Array Nat)) (p : Nat) : Array Nat := Id.run do
  let mut o : Array Nat := #[p]
  let mut h := 0
  while h < o.size do
    let x := o[h]!
    h := h + 1
    for g in gs do
      if !o.contains g[x]! then
        o := o.push g[x]!
  return o.qsort (· < ·)

meta def restrM (om g : Array Nat) : Array Nat :=
  om.map fun x => (om.findIdx? (· == g[x]!)).getD 0

end CertificateChecks.KernelC24608

end
