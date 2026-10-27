module

public import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CFSGNative.SectionRank.TitsChain
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Tits

open CFSG.SectionRank.Native.Tits

meta def ptsM : Array (Array Nat) := (orbitPts ()).map fun v => #[v]

meta def genM : Array (Array Nat) := (genTables ()).map fun t => t.map (·.toNat)

meta def reachM : Array (Array Nat) := Id.run do
  let G := genM
  let r := (orbitPts ()).findIdx? (· == 2048) |>.getD 0
  let mut seen : Array Bool := Array.replicate 1755 false
  seen := seen.set! r true
  let mut rows : Array (Array Nat) := #[#[r, 0, 0]]
  let mut h := 0
  while h < rows.size do
    let p := rows[h]![0]!
    for s in [0:4] do
      let q := G[s]![p]!
      if !seen[q]! then
        seen := seen.set! q true
        rows := rows.push #[q, h, s]
    h := h + 1
  return rows

end CertificateChecks.KernelLC.Tits

#kc_items CertificateChecks.KernelLC.Tits.TP include_bytes "data/Data.TP.items" 19054 13889954586301689919
#kc_items CertificateChecks.KernelLC.Tits.TG include_bytes "data/Data.TG.items" 9672 17672028335351280158
#kc_items CertificateChecks.KernelLC.Tits.TR include_bytes "data/Data.TR.items" 15280 15779094633519677415
