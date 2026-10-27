module

public import Certificates.Kernel.HeLoc.TreeCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.RankThree.PartOne.KS.RuFiveCheckInputs
public meta import CFSG.RankThree.PartOne.KS.RuFiveCheckInputs
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Std.Data.HashMap
public meta import CFSG.RankThree.Native.HSMcLFiveCheck
public import CFSG.RankThree.Native.HSMcLFiveCheck
public import CFSG.Sporadic.Schreier.RuDefs
public meta import CFSG.Sporadic.Schreier.RuDefs
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum

public section

namespace CertificateChecks.KernelRuFive

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne CFSG.RankThree.Native

meta def arrsM : Array (Array Nat) := Array.ofFn fun j : Fin 75 => ruFiveArr j.val

meta def invsM : Array (Array Nat) := arrsM.map (invCand 4060)

meta def evalWM (w : List Int) : Array Nat :=
  w.foldr (fun (l : Int) (acc : Array Nat) =>
    let a := if 0 < l then ruCase0Arrs[l.toNat - 1]! else invCand 4060 ruCase0Arrs[(-l).toNat - 1]!
    compA 4060 a acc) (idA 4060)

meta def transWM (i : Nat) : Array (Option (List Int)) := Id.run do
  let S := ruCase0Arrs
  let base := ruCase0BaseArr
  let idx := (List.range S.size).filter fun j =>
    (List.range i).all fun t => (S[j]!)[base[t]!]! == base[t]!
  let steps : Array (Array Nat × Int) :=
    (idx.map fun j => (S[j]!, ((j + 1 : Nat) : Int))).toArray ++
      (idx.map fun j => (invCand 4060 S[j]!, -((j + 1 : Nat) : Int))).toArray
  let root := base[i]!
  let mut wt : Array (Option (List Int)) := (Array.replicate 4060 none).set! root (some [])
  let mut q : Array Nat := #[root]
  let mut h := 0
  while h < q.size do
    let x := q[h]!
    let wx := (wt[x]!).getD []
    for st in steps do
      let y := st.1[x]!
      if (wt[y]!).isNone then
        wt := wt.set! y (some (st.2 :: wx))
        q := q.push y
    h := h + 1
  return wt

meta def transM : Array (Array (Option (List Int))) := (Array.range 9).map transWM

meta def siftWM (g0 : Array Nat) : List Int := Id.run do
  let mut g := g0
  let mut acc : List Int := []
  for i in [0:9] do
    let y := g[ruCase0BaseArr[i]!]!
    let w := ((transM[i]!)[y]!).getD []
    g := compA 4060 (invCand 4060 (evalWM w)) g
    acc := acc ++ w
  return acc

meta def codeM (l : Int) : Nat := if 0 < l then 2 * (l.toNat - 1) else 2 * ((-l).toNat - 1) + 1

meta def wordsM : List Nat := arrsM.toList.foldr (fun g acc =>
  let w := siftWM g
  w.length :: (w.map codeM ++ acc)) []

meta def forceOf (rels : List (Nat × Nat × Nat)) (nb : Nat) : List Nat :=
  (List.range nb).map fun i =>
    match rels.find? (fun r => r.2.1 == i && decide (r.1 < i)) with
    | some r => 8 * r.1 + r.2.2 + 1
    | none => 0

meta def idxOf (c : CFSG.Monster.B.Fischer.ArrCert) (t : Array Nat) : Nat :=
  ((List.range c.pts.size).find? fun k => eqA 4060 c.pts[k]! t).getD 0

meta def fr0M : List Nat := forceOf ruCase0Rels 9

meta def fr1M : List Nat := forceOf ruCase1Rels 5

meta def qwM : List Nat :=
  let pw : Array (Nat × Array Nat) := Id.run do
    let mut r := #[]
    for j in [0:31] do
      for e in [1:5] do
        r := r.push (8 * j + e, CFSG.Monster.B.Mathieu.powArr 4060 ruFiveLines[j]! e)
    return r
  ruFiveQCert.pts.toList.map fun t =>
    ((pw.toList.find? fun c => eqA 4060 t c.2).map (·.1)).getD 0

meta def lqM : List Nat := (List.range 31).map fun j => idxOf ruFiveQCert ruFiveLines[j]!

meta def awM : List Nat := ruFiveA0Gens.toList.map (idxOf ruFiveC0Cert)

meta def cwM : List Nat := (List.range 9).map fun m =>
  idxOf ruFiveA0Cert (conjA 4060 ruFiveC0Gens[m / 3]! ruFiveA0Gens[m % 3]!)

meta def xwM : List Nat := [idxOf ruFiveA0Cert ruFiveLines[0]!]

meta def zw0M : List Nat := ruFiveC0Cert.pts.toList.map fun c =>
  match (List.range 3).find? (fun l => !commA 4060 c ruFiveA0Gens[l]!) with
  | some l => l + 1
  | none => ((List.range 5).find? (fun e =>
      eqA 4060 c (CFSG.Monster.B.Mathieu.powArr 4060 ruFiveLines[0]! e))).getD 0 + 100

meta def cdM : List Nat := ruFiveDWit.toList.map (idxOf ruFiveC1Cert)

meta def dkM : List Nat := (List.range 6).map fun m =>
  idxOf ruFiveDCert (conjA 4060 ruFiveC1Gens[m / 2]! ruFiveDGens[m % 2]!)

meta def dcM : List Nat := (List.range 9).map fun m =>
  idxOf ruFiveDCert (commutatorA 4060 ruFiveC1Gens[m / 3]! ruFiveC1Gens[m % 3]!)

meta def zw1M : List Nat := ruFiveC1Cert.pts.toList.map fun c =>
  match (List.range 2).find? (fun l => !commA 4060 c ruFiveDGens[l]!) with
  | some l => l + 1
  | none => ((List.range 5).find? (fun e =>
      eqA 4060 c (CFSG.Monster.B.Mathieu.powArr 4060 ruFiveLines[1]! e))).getD 0 + 100

meta def dIdx : Std.HashMap Nat Nat :=
  (List.range ruFiveDCert.pts.size).foldl (fun m i =>
    m.insert (keyA 4060 ruFiveKeys ruFiveDCert.pts[i]!) i) {}

meta def dOf (t : Array Nat) : Nat := dIdx.getD (keyA 4060 ruFiveKeys t) 0

meta def mtM : Array (Array Nat) := (Array.range 60).map fun a => (Array.range 60).map fun b =>
  dOf (compA 4060 ruFiveDCert.pts[a]! ruFiveDCert.pts[b]!)

meta def ivM : Array (Array Nat) :=
  #[(Array.range 60).map fun a => dOf (invCand 4060 ruFiveDCert.pts[a]!)]

meta def btM : Array (Array Nat) := (Array.range 60).map fun r => Id.run do
  if r == 0 then return Array.replicate 60 0
  let cj := fun j : Nat => (mtM[(mtM[j]!)[r]!]!)[(ivM[0]!)[j]!]!
  let mut par : Array Nat := Array.replicate 60 0
  let mut lab : Array Nat := Array.replicate 60 0
  let mut dep : Array Nat := Array.replicate 60 0
  let mut seen : Array Bool := (Array.replicate 60 false).set! 0 true
  let mut q : Array Nat := #[0]
  let mut h := 0
  while h < q.size do
    let i := q[h]!
    for j in [0:60] do
      let y := (mtM[cj j]!)[i]!
      if !seen[y]! then
        seen := seen.set! y true
        par := par.set! y i
        lab := lab.set! y j
        dep := dep.set! y (dep[i]! + 1)
        q := q.push y
    h := h + 1
  return (Array.range 60).map fun i => par[i]! + 256 * lab[i]! + 65536 * dep[i]!

end CertificateChecks.KernelRuFive

set_option maxRecDepth 400000

#kss_perms CertificateChecks.KernelRuFive.AIF 12 CertificateChecks.KernelRuFive.invsM
#knatlist CertificateChecks.KernelRuFive.WF CertificateChecks.KernelRuFive.wordsM
#kh_tree CertificateChecks.KernelRuFive.Q CFSG.RankThree.PartOne.ruFiveQCert 4060
  CFSG.RankThree.PartOne.ruFiveKeys
#kh_tree CertificateChecks.KernelRuFive.C0 CFSG.RankThree.PartOne.ruFiveC0Cert 4060
  CFSG.RankThree.PartOne.ruFiveKeys
#kh_tree CertificateChecks.KernelRuFive.C1 CFSG.RankThree.PartOne.ruFiveC1Cert 4060
  CFSG.RankThree.PartOne.ruFiveKeys
#kh_tree CertificateChecks.KernelRuFive.A0 CFSG.RankThree.PartOne.ruFiveA0Cert 4060
  CFSG.RankThree.PartOne.ruFiveKeys
#kh_tree CertificateChecks.KernelRuFive.D0 CFSG.RankThree.PartOne.ruFiveDCert 4060
  CFSG.RankThree.PartOne.ruFiveKeys
#knatlist CertificateChecks.KernelRuFive.FR0 CertificateChecks.KernelRuFive.fr0M
#knatlist CertificateChecks.KernelRuFive.FR1 CertificateChecks.KernelRuFive.fr1M
#knatlist CertificateChecks.KernelRuFive.QW CertificateChecks.KernelRuFive.qwM
#knatlist CertificateChecks.KernelRuFive.LQ CertificateChecks.KernelRuFive.lqM
#knatlist CertificateChecks.KernelRuFive.AW CertificateChecks.KernelRuFive.awM
#knatlist CertificateChecks.KernelRuFive.CW CertificateChecks.KernelRuFive.cwM
#knatlist CertificateChecks.KernelRuFive.XW CertificateChecks.KernelRuFive.xwM
#knatlist CertificateChecks.KernelRuFive.ZW0 CertificateChecks.KernelRuFive.zw0M
#knatlist CertificateChecks.KernelRuFive.CD CertificateChecks.KernelRuFive.cdM
#knatlist CertificateChecks.KernelRuFive.DK CertificateChecks.KernelRuFive.dkM
#knatlist CertificateChecks.KernelRuFive.DC CertificateChecks.KernelRuFive.dcM
#knatlist CertificateChecks.KernelRuFive.ZW1 CertificateChecks.KernelRuFive.zw1M
#kmisc_packarrs CertificateChecks.KernelRuFive.MT CertificateChecks.KernelRuFive.mtM 8
#kmisc_packarrs CertificateChecks.KernelRuFive.IV CertificateChecks.KernelRuFive.ivM 8
#kmisc_packarrs CertificateChecks.KernelRuFive.BT CertificateChecks.KernelRuFive.btM 20

end
