module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.Q3ATitsCheck
meta import CFSG.Sporadic.SuzRecog.Q3ATitsCheck
public meta import CFSG.Sporadic.SuzRecog.Q3ACheck
public meta import Certificates.Data.SuzModelGroupsInputs
public meta import Certificates.Data.SuzQ3ATitsData

public section

namespace CertificateChecks.KernelSpor.Q3APins

open CFSG.Sporadic.SuzRecog.Q3A.Check CFSG.Monster.B.Co2.Native

meta def fM : Array (Array Nat) := Id.run do
  let mut a : Array (Array Nat) := #[fix0]
  for i in [1:22880] do
    a := a.push (imgA (bA tlab[i]!) a[tpar[i]!]!)
  return a

meta def kmM : Std.HashMap UInt64 Nat := Id.run do
  let mut m : Std.HashMap UInt64 Nat := ∅
  for i in [0:22880] do
    m := m.insert (keyOf fM[i]!) i
  return m

meta def actM (g : Array Nat) (i : Nat) : Nat := kmM.getD (keyOf (imgA g fM[i]!)) 22880

meta def cM (i : Nat) : Array Nat := Id.run do
  let mut path : Array Nat := #[]
  let mut j := i
  for _ in [0:64] do
    if j != 0 then
      path := path.push j
      j := tpar[j]!
  let mut c := idA 1782
  for k in [0:path.size] do
    let v := path[path.size - 1 - k]!
    c := compA 1782 (bA tlab[v]!) c
  return c

meta def ciM (i : Nat) : Array Nat := invCand 1782 (cM i)

meta def n0M : Array Nat := (Array.range 22880).filter fun y => froot[y]! == 10

meta def dM (y : Nat) : Nat :=
  let r := froot[y]!
  if r == 0 then 0 else if r == 10 then 1 else if r == 202 then 3 else 2

meta def nbrsM (i : Nat) : Array Nat := let c := cM i; n0M.map (actM c)

meta def rtM : Array Nat := #[1, 2, 202]

meta def posM (r : Nat) : Array Nat :=
  let nb := nbrsM r
  let d := dM r
  (Array.range 486).filter fun t => dM nb[t]! + 1 == d

meta def dsM (r : Nat) : Array Nat := let nb := nbrsM r; (posM r).map fun t => nb[t]!

meta def adjM (ci : Array Nat) (j : Nat) : Bool := froot[actM ci j]! == 10

meta def fPin : Array (Array Nat) := fM

meta def kPin : Array (Array Nat) :=
  let ks := (Array.range 22880).map fun i => ((keyOf fM[i]!).toNat, i)
  (ks.qsort fun a b => a.1 < b.1).map fun p => #[p.1, p.2]

meta def wPin : Array (Array Nat) := #[wt.map UInt64.toNat]

meta def nPin : Array (Array Nat) := #[n0M]

meta def iPin : Array (Array Nat) :=
  (#[b0, b1, CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr, x1, x2,
    CFSG.Sporadic.SuzRecog.Q3ATitsData.tau0Arr, CFSG.Sporadic.SuzRecog.Q3ATitsData.rho0Arr,
    CFSG.Sporadic.SuzRecog.Q3ATitsData.stab0Arr, CFSG.Sporadic.SuzRecog.Q3ATitsData.stab1Arr,
    CFSG.Sporadic.SuzRecog.Q3ATitsData.stab2Arr, CFSG.Sporadic.SuzRecog.LevelTwoData.w0Arr,
    CFSG.Sporadic.SuzRecog.ModelGroupsData.s1Arr,
    CFSG.Sporadic.SuzRecog.ModelGroupsData.s2Arr]).map (invCand 1782)

meta def pPin : Array (Array Nat) := rtM.map posM

meta def dPin : Array (Array Nat) := rtM.map dsM

meta def parentsM (k : Nat) : Array Nat :=
  let t := spanPin rtM[k]!
  (Array.range t.1.size).filter fun a => (Array.range t.1.size).any fun b => b != 0 && t.1[b]! == a

meta def ciPin : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := Array.replicate 1537 #[0]
  for k in [0:3] do
    let ds := dsM rtM[k]!
    let ps := parentsM k
    for a in [0:ds.size] do
      if ps.contains a || k < 2 then
        out := out.set! (512 * k + a) (ciM ds[a]!)
  out := out.set! 1536 (ciM (actM CFSG.Sporadic.SuzRecog.LevelTwoData.w0Arr 0))
  return out

meta def qPin : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := Array.replicate 1024 #[0]
  for k in [0:2] do
    let r := rtM[k]!
    let nb := nbrsM r
    let ds := dsM r
    let cis := ds.map ciM
    for t in [0:486] do
      let g := nb[t]!
      if dM g == 2 then
        match (Array.range ds.size).find? fun a => adjM cis[a]! g with
        | some a => out := out.set! (512 * k + t) #[1 + 4 * a]
        | none =>
          let ng := nbrsM g
          let mut w := 0
          for a in [0:ds.size] do
            for u in [0:486] do
              if w == 0 && froot[ng[u]!]! == 10 && adjM cis[a]! ng[u]! then
                w := 2 + 4 * a + 128 * u
          out := out.set! (512 * k + t) #[w]
  return out

end CertificateChecks.KernelSpor.Q3APins

#kmisc_packarrs CertificateChecks.KernelSpor.Q3AF CertificateChecks.KernelSpor.Q3APins.fPin 11
#kmisc_packarrs CertificateChecks.KernelSpor.Q3AK CertificateChecks.KernelSpor.Q3APins.kPin 64
#kmisc_packarrs CertificateChecks.KernelSpor.Q3AW CertificateChecks.KernelSpor.Q3APins.wPin 64
#kmisc_packarrs CertificateChecks.KernelSpor.Q3AN CertificateChecks.KernelSpor.Q3APins.nPin 15
#kmisc_packarrs CertificateChecks.KernelSpor.Q3AI CertificateChecks.KernelSpor.Q3APins.iPin 11
#kmisc_packarrs CertificateChecks.KernelSpor.Q3AP CertificateChecks.KernelSpor.Q3APins.pPin 10
#kmisc_packarrs CertificateChecks.KernelSpor.Q3AD CertificateChecks.KernelSpor.Q3APins.dPin 15
#kmisc_packarrs CertificateChecks.KernelSpor.Q3ACI CertificateChecks.KernelSpor.Q3APins.ciPin 11
#kmisc_packarrs CertificateChecks.KernelSpor.Q3AQ CertificateChecks.KernelSpor.Q3APins.qPin 32

end
