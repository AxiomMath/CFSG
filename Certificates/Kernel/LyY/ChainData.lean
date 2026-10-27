module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.LyY.Words
public meta import Certificates.Kernel.LyY.Words
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamYInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyY

open CFSG.Sporadic.Recognition.LyonsSims

meta def natA (t : CFSG.Sporadic.Th.Native.Table) : Array Nat := t.map (·.toNat)

meta def compM (t u : Array Nat) : Array Nat := Array.ofFn (n := 1080) fun i => t[u[i.val]!]!

meta def invM (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 1080 0
  for i in [0:1080] do
    r := r.set! t[i]! i
  return r

meta def abM : Array (Array Nat) := #[natA Ly1080.uTabs[0]!, natA Ly1080.uTabs[3]!]

meta def wordM (wd : List Int) : Array Nat :=
  wd.foldr (fun (l : Int) acc =>
    compM (if 0 < l then abM[l.toNat - 1]! else invM abM[(-l).toNat - 1]!) acc) (Array.range 1080)

meta def yStrongM : Array (Array Nat) := abM ++ (yD.map wordM).toArray

end CertificateChecks.KernelLyY

#ks_rawchain_sl2_data CertificateChecks.KernelLyY.YC 1080 11 60 120
  CertificateChecks.KernelLyY.yStrongM CertificateChecks.KernelLyY.yBase 2
  CertificateChecks.KernelLyY.yD

end
