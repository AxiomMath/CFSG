module

public import Certificates.Data.DcHeC0
public import Certificates.Kernel.He589203.Q
public import CFSG.Sporadic.HeldB.HeBlocks

public section

namespace CFSG.KD.He589208

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.HeC0
open CFSG.QuasithinUnique.K1.SporadicPerm (slpTabsA)
open CFSG.KD.He589203 (recOf rowsOf skOf lowB orbOrder recVs ihOf)

@[expose] def slp : Array (Array Nat) := slpTabsA ta tb prog

@[expose] def perms : Array (Array Nat) :=
  let Q := orbOrder 8330 RT
  #[invTab ta, invTab tb] ++ RT.map invTab ++ #[orbitLabels 8330 RT, Q, invTab Q]

@[expose] def recR : Array (Array Nat) := recOf 8330 B RT enumR.1 enumR.2 #[]

@[expose] def skR : Array Nat := skOf 8330 (rowsOf B RT enumR.1 enumR.2)

@[expose] def recV : Array (Array (Array Nat)) := recVs heC0Dc

@[expose] def recV0 : Array (Array Nat) := recV[0]!

@[expose] def recV1 : Array (Array Nat) := recV[1]!

@[expose] def hpos : Array (Array Nat) :=
  let D := heC0Dc
  let cks := (Array.range D.reps.size).map fun j =>
    (conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi j) (D.X j)).toArray
  (Array.range D.NR).map fun k => cks.map fun ks => lowB skR ks[k]! 0 skR.size

@[expose] def ih : Array (Array Nat) := ihOf heC0Dc

def nfOf (g : Array Nat) : Nat :=
  let nf := CFSG.Sporadic.Schreier.PairNative.decodeNF CFSG.Sporadic.HeldB.heLevels
    ((CFSG.Sporadic.HeldB.heBase.map fun b => g[b]!).toArray)
  (List.range nf.size).foldl (fun acc i => acc ||| (nf[i]! <<< (16 * i))) 0

def nfs : List Nat := [nfOf ta, nfOf tb]

end CFSG.KD.He589208

end
