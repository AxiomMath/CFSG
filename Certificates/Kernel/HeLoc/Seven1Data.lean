module

public import Certificates.Kernel.HeLoc.Seven0Data
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.PartOne.KS.PKitSimple
public meta import CFSG.RankThree.PartOne.KS.PKitSimple
public meta import Std.Data.HashMap

public section

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne CFSG.RankThree.Native

meta def fr1M : List Nat := forceOf heSevenCase1Rels 10

meta def cd1M : List Nat := heSevenDWit1.toList.map (idxOf heSevenC1Cert)

meta def dk1M : List Nat := (List.range 6).map fun m =>
  idxOf heSevenDCert1 (conjA 8330 heSevenC1Gens[m / 2]! heSevenDGens1[m % 2]!)

meta def dc1M : List Nat := (List.range 9).map fun m =>
  idxOf heSevenDCert1 (commutatorA 8330 heSevenC1Gens[m / 3]! heSevenC1Gens[m % 3]!)

meta def zw1M : List Nat := heSevenC1Cert.pts.toList.map fun c =>
  match (List.range 2).find? (fun l => !commA 8330 c heSevenDGens1[l]!) with
  | some l => l + 1
  | none => ((List.range 7).find? (fun e =>
      eqA 8330 c (CFSG.Monster.B.Mathieu.powArr 8330 heSevenLines[1]! e))).getD 0 + 100

meta def zwp1M : Array (Array Nat) := #[zw1M.toArray]

meta def ckv1M : Array (Array Nat) := #[heSevenC1Cert.pts.map (keyA 8330 heSevenKeys)]

meta def ep1M : List Nat :=
  let b := (heSevenCase1Base.map Fin.val).getD 0 0
  ((List.range 8330).filter fun q => (heSevenLines[1]!)[q]! == q).map fun q =>
    ((List.range 1176).find? fun j => (heSevenC1Cert.pts[j]!)[b]! == q).getD 0

meta def eq1M : List Nat :=
  let b0 := (heSevenCase1Base.map Fin.val).getD 0 0
  let b1 := (heSevenCase1Base.map Fin.val).getD 1 0
  let hs := (List.range 1176).filter fun j => (heSevenC1Cert.pts[j]!)[b0]! == b0
  (hs.foldl (fun (acc : List Nat × List Nat) j =>
    let q := (heSevenC1Cert.pts[j]!)[b1]!
    if acc.1.contains q then acc else (q :: acc.1, j :: acc.2)) ([], [])).2.reverse

meta def dIdx: Std.HashMap Nat Nat :=
  (List.range heSevenDCert1.pts.size).foldl (fun m i =>
    m.insert (keyA 8330 heSevenKeys heSevenDCert1.pts[i]!) i) {}

meta def dOf (t : Array Nat) : Nat := dIdx.getD (keyA 8330 heSevenKeys t) 0

meta def mt1M : Array (Array Nat) := (Array.range 168).map fun a => (Array.range 168).map fun b =>
  dOf (compA 8330 heSevenDCert1.pts[a]! heSevenDCert1.pts[b]!)

meta def iv1M : Array (Array Nat) :=
  #[(Array.range 168).map fun a => dOf (invCand 8330 heSevenDCert1.pts[a]!)]

meta def rp1M : List Nat := classReps 8330 heSevenDCert1

meta def bt1M : Array (Array Nat) := rp1M.toArray.map fun r => Id.run do
  let cj := fun j : Nat =>
    (mt1M[(mt1M[j]!)[r]!]!)[dOf (invCand 8330 heSevenDCert1.pts[j]!)]!
  let mut par : Array Nat := Array.replicate 168 0
  let mut lab : Array Nat := Array.replicate 168 0
  let mut dep : Array Nat := Array.replicate 168 0
  let mut seen : Array Bool := (Array.replicate 168 false).set! 0 true
  let mut q : Array Nat := #[0]
  let mut h := 0
  while h < q.size do
    let i := q[h]!
    for j in [0:168] do
      let y := (mt1M[cj j]!)[i]!
      if !seen[y]! then
        seen := seen.set! y true
        par := par.set! y i
        lab := lab.set! y j
        dep := dep.set! y (dep[i]! + 1)
        q := q.push y
    h := h + 1
  return (Array.range 168).map fun i => par[i]! + 256 * lab[i]! + 65536 * dep[i]!

end CertificateChecks.KernelHeLoc.Seven

#kh_tree CertificateChecks.KernelHeLoc.Seven.C1 CFSG.RankThree.PartOne.heSevenC1Cert 8330
  CFSG.RankThree.PartOne.heSevenKeys
#kh_tree CertificateChecks.KernelHeLoc.Seven.D1 CFSG.RankThree.PartOne.heSevenDCert1 8330
  CFSG.RankThree.PartOne.heSevenKeys
#knatlist CertificateChecks.KernelHeLoc.Seven.FR1 CertificateChecks.KernelHeLoc.Seven.fr1M
#knatlist CertificateChecks.KernelHeLoc.Seven.CD1 CertificateChecks.KernelHeLoc.Seven.cd1M
#knatlist CertificateChecks.KernelHeLoc.Seven.EP1 CertificateChecks.KernelHeLoc.Seven.ep1M
#knatlist CertificateChecks.KernelHeLoc.Seven.EQ1 CertificateChecks.KernelHeLoc.Seven.eq1M
#knatlist CertificateChecks.KernelHeLoc.Seven.DK1 CertificateChecks.KernelHeLoc.Seven.dk1M
#knatlist CertificateChecks.KernelHeLoc.Seven.DC1 CertificateChecks.KernelHeLoc.Seven.dc1M
#kmisc_packarrs CertificateChecks.KernelHeLoc.Seven.ZWP1 CertificateChecks.KernelHeLoc.Seven.zwp1M 8
#kmisc_packarrs CertificateChecks.KernelHeLoc.Seven.CKV1 CertificateChecks.KernelHeLoc.Seven.ckv1M 184
#kmisc_packarrs CertificateChecks.KernelHeLoc.Seven.MT1 CertificateChecks.KernelHeLoc.Seven.mt1M 8
#kmisc_packarrs CertificateChecks.KernelHeLoc.Seven.IV1 CertificateChecks.KernelHeLoc.Seven.iv1M 8
#knatlist CertificateChecks.KernelHeLoc.Seven.RP1 CertificateChecks.KernelHeLoc.Seven.rp1M
#kmisc_packarrs CertificateChecks.KernelHeLoc.Seven.BT1 CertificateChecks.KernelHeLoc.Seven.bt1M 20

end
