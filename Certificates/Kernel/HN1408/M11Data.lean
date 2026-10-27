module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.HN1408.RecGen

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.M11Gen

open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.RecGen CFSG.PSL3Four.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def gA : Array (Array Nat) := gensM [y0Word, vWord]
meta def gAI : Array (Array Nat) := gA.map invM
meta def iA : Array (Array Nat) := idsOf gA
meta def rA : Array (Array Nat) := recOf gA
meta def cA : Array (Array Nat) := clOf gA

meta def zR : Array Nat := natArr (tabW classz.rep)
meta def azR : Array Nat := natArr (tabW classaz.rep)

meta def invs : Array (Array Nat) :=
  (gensM [y0Word, vWord, n1Word, ck2Word, ck3Word, ck4Word, cBWord]).map invM

meta def toT (x : Array Nat) : Table := x.map UInt32.ofNat

meta def ordW : Array (Array Nat) :=
  rA.map fun x =>
    let t := toT x
    #[([8, 6, 5, 11].find? fun e => tblEq 1408 (powT 1408 e t) (idT 1408)).getD 0]

meta def jOf (m : Std.HashMap (Array Nat) Nat) (x : Array Nat) : Array Nat :=
  let tj := toT x
  match m.get? x with
  | some k => #[0, k, 0, 0, 0, 0]
  | none =>
    let n1 := tabW n1Word
    match m.get? (natArr (conjT 1408 n1 (invT 1408 n1) tj)) with
    | some k => #[1, k, 0, 0, 0, 0]
    | none =>
      let ys := powsT (tabW y0Word)
      let k := (m11Probes.findIdx? fun p => !ordInS (idT 1408) (probeT ys tj p)).getD 6
      let q := probeT ys tj (m11Probes.getD k [])
      let pts := [8, 6, 5, 11].map fun e =>
        let r := powT 1408 e q
        ((List.range 1408).find? fun i => (r[i]!).toNat != i).getD 0
      #[2, k] ++ pts.toArray

meta def yP : Array (Array Nat) := Id.run do
  let y := natArr (tabW y0Word)
  let mut a : Array (Array Nat) := #[idM]
  for _ in [0:11] do
    a := a.push (comp 1408 y a.back!)
  return a

meta def cy (k : Nat) (x : Array Nat) : Array Nat := comp 1408 yP[k]! (comp 1408 x yP[11 - k]!)

meta def clsReps (root : Array Nat) : Array (Array Nat) × Array (Array Nat) := Id.run do
  let mut reps : Array (Array Nat) := #[root]
  let mut par : Array (Array Nat) := #[#[0, 0, 0]]
  let mut seen : Std.HashSet (Array Nat) := {}
  for k in [0:11] do
    seen := seen.insert (cy k root)
  let mut i := 0
  while i < reps.size do
    let r := reps[i]!
    for k in [0:11] do
      let x := cy k r
      for j in [0:7] do
        let t := conjTab 1408 g7[j]! g7[j]! x
        if !seen.contains t then
          reps := reps.push t
          par := par.push #[i, k, j]
          for k' in [0:11] do
            seen := seen.insert (cy k' t)
    i := i + 1
  return (reps, par)

meta def keyOf (x : Array Nat) : Nat :=
  x[0]! + 2048 * x[1]! + 2048 ^ 2 * x[2]! + 2048 ^ 3 * x[3]!

meta def sortedOf (reps : Array (Array Nat)) : Array (Array Nat) :=
  let ps := (List.range reps.size).flatMap fun i => (List.range 11).map fun k =>
    (keyOf (cy k reps[i]!), i, k)
  (ps.toArray.qsort fun a b => a.1 < b.1).map fun (_, i, k) => #[i, k]

meta def repsZ : Array (Array Nat) × Array (Array Nat) := clsReps zR
meta def repsAZ : Array (Array Nat) × Array (Array Nat) := clsReps azR
meta def rZ : Array (Array Nat) := repsZ.1
meta def pZ : Array (Array Nat) := repsZ.2
meta def sZ : Array (Array Nat) := sortedOf repsZ.1
meta def wZ : Array (Array Nat) := let m := posIn rA; repsZ.1.map (jOf m)
meta def rAZ : Array (Array Nat) := repsAZ.1
meta def pAZ : Array (Array Nat) := repsAZ.2
meta def sAZ : Array (Array Nat) := sortedOf repsAZ.1
meta def wAZ : Array (Array Nat) := let m := posIn rA; repsAZ.1.map (jOf m)

meta def posW : Array (Array Nat) := posOf rA (gensM [i0Word, rho0Word, ck2Word, ck3Word, ck4Word])

end CFSG.KD.HN1408.M11Gen

end

set_option maxRecDepth 400000

#kmulh CFSG.KD.HN1408.MR1 1408 11 CFSG.KD.HN1408.M11Gen.iA CFSG.KD.HN1408.M11Gen.gA
  CFSG.KD.HN1408.RecGen.idM 1000000
#kfind CFSG.KD.HN1408.MR1Cl CFSG.KD.HN1408.M11Gen.rA CFSG.KD.HN1408.M11Gen.cA
#kmisc_packarrs CFSG.KD.HN1408.MR1I CFSG.KD.HN1408.M11Gen.gAI 11

#kmisc_packarrs CFSG.KD.HN1408.MInv CFSG.KD.HN1408.M11Gen.invs 11
#kmisc_packarrs CFSG.KD.HN1408.MYP CFSG.KD.HN1408.M11Gen.yP 11
#kmisc_packarrs CFSG.KD.HN1408.MO CFSG.KD.HN1408.M11Gen.ordW 8
#kmisc_packarrs CFSG.KD.HN1408.MW CFSG.KD.HN1408.M11Gen.posW 32

#kmisc_packarrs CFSG.KD.HN1408.MRZ CFSG.KD.HN1408.M11Gen.rZ 11
#kmisc_packarrs CFSG.KD.HN1408.MPZ CFSG.KD.HN1408.M11Gen.pZ 16
#kmisc_packarrs CFSG.KD.HN1408.MSZ CFSG.KD.HN1408.M11Gen.sZ 16
#kmisc_packarrs CFSG.KD.HN1408.MWZ CFSG.KD.HN1408.M11Gen.wZ 16
#kmisc_packarrs CFSG.KD.HN1408.MRAZ CFSG.KD.HN1408.M11Gen.rAZ 11
#kmisc_packarrs CFSG.KD.HN1408.MPAZ CFSG.KD.HN1408.M11Gen.pAZ 16
#kmisc_packarrs CFSG.KD.HN1408.MSAZ CFSG.KD.HN1408.M11Gen.sAZ 16
#kmisc_packarrs CFSG.KD.HN1408.MWAZ CFSG.KD.HN1408.M11Gen.wAZ 16
