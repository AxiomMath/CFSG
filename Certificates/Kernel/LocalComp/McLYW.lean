module

public import Certificates.Kernel.LocalComp.McLY
public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.Certificates.Kernel.LocalCompPinSound
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuterCheckInputs

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.McLY

open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

meta def yGL : List (Array Nat) := mclYGens.toList

meta def yGIM : Array (Array Nat) := mclYInvs

meta def yXM : Array (Array Nat) :=
  (Array.range 10).map fun l => wordTabS 11 mclYGens (mclYWords.getD l [])

meta def yAM : Array (Array Nat) := mclYOrbits.foldl (fun acc e => acc ++ e.tabs) #[]

meta def yAEM : Array (Array Nat) := mclYOrbits.foldl (fun acc e => Id.run do
  let idx : Std.HashMap (Array Nat) Nat :=
    (List.range e.tabs.size).foldl (fun m i => m.insert e.tabs[i]! i) {}
  let rows := e.tabs.map fun t => (List.range 4).toArray.map fun k =>
    idx.getD (conjTab 11 mclYGens[k]! mclYInvs[k]! t) 0
  return acc ++ rows) #[]

meta def pk (t : Array Nat) : Nat := t.toList.foldr (fun a acc => a + 16 * acc) 0

meta def yASM : Array (Array Nat) := mclYOrbits.foldl (fun acc e =>
  acc ++ ((Array.range e.tabs.size).qsort fun a b => pk e.tabs[a]! < pk e.tabs[b]!).map
    fun i => #[i]) #[]

meta def yCM : Array (Array Nat) := Id.run do
  let mut idx : Std.HashMap (Array Nat) (Nat × Nat) := {}
  for l in [0:mclYOrbits.size] do
    let T := mclYOrbits[l]!.tabs
    for p in [0:T.size] do
      idx := idx.insert T[p]! (l, p)
  return mclYEnum.tabs.map fun t => let q := idx.getD t (0, 0); #[q.1, q.2]

end CertificateChecks.KernelLC.McLY

#lc_bfs CertificateChecks.KernelLC.McLY.YE CertificateChecks.KernelLC.McLY.yGL 11 4
#kmisc_packarrs CertificateChecks.KernelLC.McLY.YGI CertificateChecks.KernelLC.McLY.yGIM 4
#kmisc_packarrs CertificateChecks.KernelLC.McLY.YX CertificateChecks.KernelLC.McLY.yXM 4
#kmisc_packarrs CertificateChecks.KernelLC.McLY.YA CertificateChecks.KernelLC.McLY.yAM 4
#kmisc_packarrs CertificateChecks.KernelLC.McLY.YAE CertificateChecks.KernelLC.McLY.yAEM 16
#kmisc_packarrs CertificateChecks.KernelLC.McLY.YAS CertificateChecks.KernelLC.McLY.yASM 16
#kmisc_packarrs CertificateChecks.KernelLC.McLY.YC CertificateChecks.KernelLC.McLY.yCM 16

public section

namespace CertificateChecks.KernelLC.McLY

@[expose] def yOff (l : Nat) : Nat :=
  [0, 1, 166, 606, 1596, 3180, 4500, 5490, 6480, 7200].getD l 0

@[expose] def ySz (l : Nat) : Nat := [1, 165, 440, 990, 1584, 1320, 990, 990, 720, 720].getD l 0

end CertificateChecks.KernelLC.McLY
