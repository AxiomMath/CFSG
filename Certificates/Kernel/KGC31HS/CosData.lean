module

public import Certificates.Kernel.KGC31HS.Data
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Kernel.KGC31HS.Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

namespace CertificateChecks.KernelKGC31HS.CosE

open CFSG.KS.SporSch.MOCG CFSG.Quasithin.KGC31.HS CertificateChecks.KernelKGC31HS

meta def cb : Array (Array Nat) := Id.run do
  let gs := caGenW.map gw
  let mut seen : Std.HashSet (Array Nat) := (∅ : Std.HashSet (Array Nat)).insert (idA 100)
  let mut pts : Array (Array Nat) := #[idA 100]
  let mut h := 0
  while h < pts.size do
    let y := pts[h]!
    h := h + 1
    for g in gs do
      let z := comp g y
      if !seen.contains z then
        seen := seen.insert z
        pts := pts.push z
  return pts

meta def span (bs : List (Array Nat)) : Std.HashSet (Array Nat) :=
  bs.foldl (fun S b => S.fold (fun T x => T.insert (comp b x)) S)
    ((∅ : Std.HashSet (Array Nat)).insert (idA 100))

meta def norm (bs : List (Array Nat)) (S : Std.HashSet (Array Nat)) (g : Array Nat) : Bool :=
  bs.all fun b => S.contains (comp (comp g b) (invA g))

meta def counts (ws rs : List (List Int)) : List Nat :=
  let bs := ws.map gw
  let S := span bs
  let C := cb
  rs.map fun r => (C.filter fun c => norm bs S (comp (gw r) c)).size

meta def k16 : List Nat := counts u16W u16CosetW
meta def k8 : List Nat := counts u8W u8CosetW

end CertificateChecks.KernelKGC31HS.CosE

public section

#kc_items CertificateChecks.KernelKGC31HS.K16 include_bytes "data/CosData.K16.items" 90 12467503709032886496
#kc_items CertificateChecks.KernelKGC31HS.K8 include_bytes "data/CosData.K8.items" 42 14089971454169184531

end
