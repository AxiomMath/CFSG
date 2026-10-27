module

public import Certificates.Kernel.Sporadic.ON.GenTab
public import Certificates.Kernel.Sporadic.ON2.GenWords
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public meta import CFSG.Sporadic.Schreier.ONCheckR3EInputs
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.Bridge.ONSurj

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON8

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.PSL3Four.Native

meta def spA : Array Nat := Data.spanIdx

meta def bfsT (gens : Array (Array Nat)) (cap : Nat) :
    Array (Array Nat) × Array Nat × Array Nat × Array Nat := Id.run do
  let mut T : Array (Array Nat) := #[spA]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut pos : Array Nat := #[]
  let mut idx : Std.HashMap (Array Nat) Nat := (∅ : Std.HashMap (Array Nat) Nat).insert spA 0
  for h in [0:cap] do
    if h < T.size then
      let t := T[h]!
      for j in [0:gens.size] do
        let x := t.map fun p => (gens[j]!)[p]!
        match idx[x]? with
        | some q => pos := pos.push q
        | none =>
          idx := idx.insert x T.size
          pos := pos.push T.size
          T := T.push x
          par := par.push h
          lab := lab.push j
    else break
  return (T, par, lab, pos)

meta def dR := bfsT dConj 200
meta def hR := bfsT hGensArr 200

meta def evalE (gens : Array (Array Nat)) (R : Array (Array Nat) × Array Nat × Array Nat × Array Nat) :
    Nat → Nat → Nat → Nat
  | 0, _, x => x
  | f + 1, k, x => if k == 0 then x else (gens[R.2.2.1[k]!]!)[evalE gens R f R.2.1[k]! x]!


meta def flat (T : Array (Array Nat)) : Array Nat := T.foldl (· ++ ·) #[]

meta def fpLen (T : Array (Array Nat)) : Nat := Id.run do
  for k in [1:155] do
    let keys := T.toList.map fun t => t.toList.take k
    if keys.eraseDups.length == keys.length then return k
  return 154

meta def idM : Array Nat := flat dR.1
meta def ihM : Array Nat := flat hR.1
meta def pdM : Array Nat := dR.2.1
meta def ldM : Array Nat := dR.2.2.1
meta def qdM : Array Nat := dR.2.2.2
meta def phM : Array Nat := hR.2.1
meta def lhM : Array Nat := hR.2.2.1
meta def qhM : Array Nat := hR.2.2.2

meta def hInvM : Array Nat := pinvCand nPts hArr

meta def asM : Array Nat :=
  let h := hArr
  let hi := hInvM
  let G := dConj
  let R := dR
  (Array.range R.1.size).map fun k =>
  let img := spA.map fun p => h[evalE G R 200 k hi[p]!]!
  match R.1.findIdx? (· == img) with
  | some u => u + 1
  | none => 0

meta def aslM : List Nat :=
  let A := asM
  (List.range 144).filter fun k => A[k]! != 0

meta def aFs : Nat → Nat → Nat :=
  let G := dConj
  let R := dR
  let asl := aslM
  fun j x => evalE G R 200 (asl.getD j 0) x

meta def moved (h : Array Nat) (G : Array (Array Nat))
    (R : Array (Array Nat) × Array Nat × Array Nat × Array Nat) (c : Nat) : Nat :=
  (((#[0, 227759, 100817] : Array Nat).toList.findIdx? fun p =>
    (Nat.repeat (fun x => h[evalE G R 200 c x]!) 7 p) != p)).getD 3

meta def htM : Array Nat :=
  let hv := hvhvArr
  let hvI := spA.map (hv[·]!)
  let h := hArr
  let G := hGensArr
  let R := hR
  (Array.range R.1.size).map fun c =>
    if R.1[c]! == spA then 0 else if R.1[c]! == hvI then 1 else 2 + moved h G R c

meta def wordsM : Array (List Int) := hWordsDH ++ #[liftWordDH] ++ mWordsDH

meta def flM : List Nat := [fpLen dR.1, fpLen hR.1]

meta def diffAt (f g : Nat → Nat) : Nat := ((List.range nPts).find? fun i => f i != g i).getD 0

meta def pairOf (m : Nat) (F G : Nat → Nat → Nat) : List Nat :=
  match (List.range m).find? (fun j => (List.range nPts).any fun i => F j i != G j i) with
  | some j => [j, diffAt (F j) (G j)]
  | none => [0, 0]

meta def witM : List Nat :=
  let v := vArr
  let z := zArr
  let h := hArr
  let m := mLiftArr
  let mw := wordArrs Data.MWords
  let dcs := dConj
  let qs := (List.range 4).toArray.map qPowArr
  let qk := fun (k x : Nat) => (qs[k]!)[x]!
  let mW := fun (j x : Nat) => (mw[j]!)[x]!
  let dc := fun (j x : Nat) => (dcs[j]!)[x]!
  let aF := aFs
  [diffAt (v[·]!) id, diffAt (v[·]!) (z[·]!), diffAt (fun x => v[h[x]!]!) (fun x => h[v[x]!]!)] ++
  pairOf 3 (fun j x => qk 1 (mW j x)) (fun j x => mW j (qk 1 x)) ++
  pairOf 3 (fun j x => qk 3 (mW j x)) (fun j x => mW j (qk 3 x)) ++
  pairOf 4 (fun j x => qk 1 (dc j x)) (fun j x => dc j (qk 1 x)) ++
  pairOf 4 (fun j x => qk 3 (dc j x)) (fun j x => dc j (qk 3 x)) ++
  pairOf 4 (fun j x => qk 1 (aF j x)) (fun j x => aF j (qk 1 x)) ++
  pairOf 4 (fun j x => qk 3 (aF j x)) (fun j x => aF j (qk 3 x)) ++
  ((List.range 4).flatMap fun k => pairOf 4 (fun j x => m[qk k (aF j x)]!)
    (fun j x => aF j (m[qk k x]!)))

meta def bTabF (f : Nat → Nat) : Array Nat :=
  let bp := bPos
  Data.quotientBlocks.map fun b => bp[f b[0]!]!

meta def abT : List (Array Nat) :=
  let m := mLiftArr
  let aF := aFs
  ((List.range 4).map fun j => bTabF (aF j)) ++ [bTabF (m[·]!)]

meta def abM : List Nat := abT.map (CFSG.KS.RawGen.pack 7)

meta def mselM : List Nat :=
  let E := m120Enum.tabs
  let A := abT.take 4
  (List.range E.size).filter fun i => A.all fun a => comp 120 E[i]! a == comp 120 a E[i]!

end CertificateChecks.KernelSpor.ON8

#kon_table CertificateChecks.KernelSpor.ON8T.ID CertificateChecks.KernelSpor.ON8.idM
#kon_table CertificateChecks.KernelSpor.ON8T.IH CertificateChecks.KernelSpor.ON8.ihM
#kon_table CertificateChecks.KernelSpor.ON8T.PD CertificateChecks.KernelSpor.ON8.pdM
#kon_table CertificateChecks.KernelSpor.ON8T.LD CertificateChecks.KernelSpor.ON8.ldM
#kon_table CertificateChecks.KernelSpor.ON8T.PH CertificateChecks.KernelSpor.ON8.phM
#kon_table CertificateChecks.KernelSpor.ON8T.LH CertificateChecks.KernelSpor.ON8.lhM
#kon_table CertificateChecks.KernelSpor.ON8T.QD CertificateChecks.KernelSpor.ON8.qdM
#kon_table CertificateChecks.KernelSpor.ON8T.QH CertificateChecks.KernelSpor.ON8.qhM
#kon_table CertificateChecks.KernelSpor.ON8T.AS CertificateChecks.KernelSpor.ON8.asM
#kon_table CertificateChecks.KernelSpor.ON8T.HT CertificateChecks.KernelSpor.ON8.htM
#kon_words CertificateChecks.KernelSpor.ON8W CertificateChecks.KernelSpor.ON8.wordsM
#knatlist CertificateChecks.KernelSpor.ON8.ASL CertificateChecks.KernelSpor.ON8.aslM
#knatlist CertificateChecks.KernelSpor.ON8.FL CertificateChecks.KernelSpor.ON8.flM
#knatlist CertificateChecks.KernelSpor.ON8.WIT CertificateChecks.KernelSpor.ON8.witM
#knatlist CertificateChecks.KernelSpor.ON8.AB CertificateChecks.KernelSpor.ON8.abM
#knatlist CertificateChecks.KernelSpor.ON8.MSel CertificateChecks.KernelSpor.ON8.mselM
