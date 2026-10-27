module

public import Certificates.Kernel.Sporadic.McLC.Data
public meta import Certificates.Kernel.Sporadic.McLC.Data

public section

namespace CertificateChecks.KernelSpor.McLC

meta def gsM : Array (Array (Array Nat)) :=
  CFSG.ClassicalInvolution.McLData.repGens.toArray.map fun gs =>
    gs.toArray.map fun t => t.map (·.toNat)

meta def gpM : Array (Array Nat) := gsM.flatten

meta def glM : Array Nat := gsM.map (·.size)

meta def goM : Array Nat := (gsM.foldl (fun (acc : Array Nat × Nat) g => (acc.1.push acc.2,
  acc.2 + g.size)) (#[], 0)).1

meta def wordTo (gs : Array (Array Nat)) (tgt : Nat × Nat × Nat) : List Nat := Id.run do
  let key := fun (p : Nat × Nat × Nat) => (p.1 * 275 + p.2.1) * 275 + p.2.2
  let mut seen : Std.HashMap Nat (List Nat) := (∅ : Std.HashMap Nat (List Nat)).insert
    (key (0, 14, 2)) []
  let mut q : Array (Nat × Nat × Nat) := #[(0, 14, 2)]
  let mut h := 0
  while h < q.size do
    let s := q[h]!
    let ws := seen.getD (key s) []
    if s == tgt then return ws
    for i in [0:gs.size] do
      let g := gs[i]!
      let s' := (g[s.1]!, g[s.2.1]!, g[s.2.2]!)
      if !(seen.contains (key s')) then
        seen := seen.insert (key s') (i :: ws)
        q := q.push s'
    h := h + 1
  return []

meta def vwM : Array (List Nat) := gsM.foldl (fun acc gs =>
  let f := fun (t : Array Nat) => (t[0]!, t[14]!, t[2]!)
  (acc.push (wordTo gs (f kgM[0]!))).push (wordTo gs (f kgM[1]!))) #[]

meta def vcM : Array Nat := (vwM.toList.flatMap id).toArray

meta def vsM : Array Nat := (vwM.foldl (fun (acc : Array Nat × Nat) w => (acc.1.push acc.2,
  acc.2 + w.length)) (#[], 0)).1

meta def vnM : Array Nat := vwM.map (·.length)

end CertificateChecks.KernelSpor.McLC

#kmisc_packarrs CertificateChecks.KernelSpor.McLC.GP CertificateChecks.KernelSpor.McLC.gpM 9
#kc_nattree CertificateChecks.KernelSpor.McLC.GL CertificateChecks.KernelSpor.McLC.glM
#kc_nattree CertificateChecks.KernelSpor.McLC.GO CertificateChecks.KernelSpor.McLC.goM
#kc_nattree CertificateChecks.KernelSpor.McLC.VC CertificateChecks.KernelSpor.McLC.vcM
#kc_nattree CertificateChecks.KernelSpor.McLC.VS CertificateChecks.KernelSpor.McLC.vsM
#kc_nattree CertificateChecks.KernelSpor.McLC.VN CertificateChecks.KernelSpor.McLC.vnM

end
