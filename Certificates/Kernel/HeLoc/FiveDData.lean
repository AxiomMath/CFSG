module

public import Certificates.Kernel.HeLoc.FiveLData
public import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
public meta import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Std.Data.HashMap

public section

namespace CertificateChecks.KernelHeLoc.FiveL

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne CFSG.RankThree.Native

meta def forceOf (rels : List (Nat × Nat × Nat)) (nb : Nat) : List Nat :=
  (List.range nb).map fun i =>
    match rels.find? (fun r => r.2.1 == i && decide (r.1 < i)) with
    | some r => 8 * r.1 + r.2.2 + 1
    | none => 0

meta def idxOf (c : CFSG.Monster.B.Fischer.ArrCert) (t : Array Nat) : Nat :=
  ((List.range c.pts.size).find? fun k => eqA 8330 c.pts[k]! t).getD 0

meta def fr5M : List Nat := forceOf heFiveCase0Rels 9

meta def cd0M : List Nat := heFiveDWit0.toList.map (idxOf heFiveC0Cert)

meta def dk0M : List Nat := (List.range 6).map fun m =>
  idxOf heFiveDCert0 (conjA 8330 heFiveC0Gens[m / 2]! heFiveDGens0[m % 2]!)

meta def dc0M : List Nat := (List.range 9).map fun m =>
  idxOf heFiveDCert0 (commutatorA 8330 heFiveC0Gens[m / 3]! heFiveC0Gens[m % 3]!)

meta def zw0M : List Nat := heFiveC0Cert.pts.toList.map fun c =>
  match (List.range 2).find? (fun l => !commA 8330 c heFiveDGens0[l]!) with
  | some l => l + 1
  | none => ((List.range 5).find? (fun e =>
      eqA 8330 c (CFSG.Monster.B.Mathieu.powArr 8330 heFiveLines[0]! e))).getD 0 + 100

meta def dIdx : Std.HashMap Nat Nat :=
  (List.range heFiveDCert0.pts.size).foldl (fun m i =>
    m.insert (keyA 8330 heFiveKeys heFiveDCert0.pts[i]!) i) {}

meta def dOf (t : Array Nat) : Nat := dIdx.getD (keyA 8330 heFiveKeys t) 0

meta def mt0M : Array (Array Nat) := (Array.range 60).map fun a => (Array.range 60).map fun b =>
  dOf (compA 8330 heFiveDCert0.pts[a]! heFiveDCert0.pts[b]!)

meta def iv0M : Array (Array Nat) :=
  #[(Array.range 60).map fun a => dOf (invCand 8330 heFiveDCert0.pts[a]!)]

meta def bt0M : Array (Array Nat) := (Array.range 60).map fun r => Id.run do
  if r == 0 then return Array.replicate 60 0
  let cj := fun j : Nat =>
    (mt0M[(mt0M[j]!)[r]!]!)[(iv0M[0]!)[j]!]!
  let mut par : Array Nat := Array.replicate 60 0
  let mut lab : Array Nat := Array.replicate 60 0
  let mut dep : Array Nat := Array.replicate 60 0
  let mut seen : Array Bool := (Array.replicate 60 false).set! 0 true
  let mut q : Array Nat := #[0]
  let mut h := 0
  while h < q.size do
    let i := q[h]!
    for j in [0:60] do
      let y := (mt0M[cj j]!)[i]!
      if !seen[y]! then
        seen := seen.set! y true
        par := par.set! y i
        lab := lab.set! y j
        dep := dep.set! y (dep[i]! + 1)
        q := q.push y
    h := h + 1
  return (Array.range 60).map fun i => par[i]! + 256 * lab[i]! + 65536 * dep[i]!

end CertificateChecks.KernelHeLoc.FiveL

#knatlist CertificateChecks.KernelHeLoc.FiveL.FR5 CertificateChecks.KernelHeLoc.FiveL.fr5M
#kh_tree CertificateChecks.KernelHeLoc.FiveL.D0 CFSG.RankThree.PartOne.heFiveDCert0 8330
  CFSG.RankThree.PartOne.heFiveKeys
#knatlist CertificateChecks.KernelHeLoc.FiveL.CD0 CertificateChecks.KernelHeLoc.FiveL.cd0M
#knatlist CertificateChecks.KernelHeLoc.FiveL.DK0 CertificateChecks.KernelHeLoc.FiveL.dk0M
#knatlist CertificateChecks.KernelHeLoc.FiveL.DC0 CertificateChecks.KernelHeLoc.FiveL.dc0M
#knatlist CertificateChecks.KernelHeLoc.FiveL.ZW0 CertificateChecks.KernelHeLoc.FiveL.zw0M
#kmisc_packarrs CertificateChecks.KernelHeLoc.FiveL.MT0 CertificateChecks.KernelHeLoc.FiveL.mt0M 8
#kmisc_packarrs CertificateChecks.KernelHeLoc.FiveL.IV0 CertificateChecks.KernelHeLoc.FiveL.iv0M 8
#kmisc_packarrs CertificateChecks.KernelHeLoc.FiveL.BT0 CertificateChecks.KernelHeLoc.FiveL.bt0M 20

end
