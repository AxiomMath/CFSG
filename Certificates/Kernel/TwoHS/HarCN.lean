module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.TwoHS.HarCD
meta import Certificates.Kernel.TwoHS.HarCD
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarCOdd
meta import Std.Data.HashSet

public section

namespace CFSG.KD.TwoHS.HarCN

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def pcSeq (els : Array (Array Nat)) (m : Nat) : Array (Array Nat) × Array (Array Nat) :=
  Id.run do
  let idm := idTab 11200
  let mut S : Array (Array Nat) := #[idm]
  let mut set : Std.HashSet (Array Nat) := Std.HashSet.emptyWithCapacity.insert idm
  let mut ys : Array (Array Nat) := #[]
  for _ in [0:m] do
    let mut found : Option (Array Nat) := none
    for y in els do
      if found.isNone && !set.contains y && set.contains (comp 11200 y y) then
        let yi := CFSG.Monster.B.Co2.Native.invCand 11200 y
        if ys.all (fun s => set.contains (comp 11200 (comp 11200 y s) yi)) then
          found := some y
    match found with
    | some y =>
      ys := ys.push y
      let S2 := S.map fun x => comp 11200 x y
      S := S ++ S2
      set := S2.foldl (fun h x => h.insert x) set
    | none => pure ()
  return (S, ys)

meta def cjOf (ys : Array (Array Nat)) : Array (Array Nat) :=
  ((List.range ys.size).toArray.map fun r => (List.range ys.size).toArray.map fun s =>
    if s < r then
      comp 11200 (comp 11200 ys[r]! ys[s]!) (CFSG.Monster.B.Co2.Native.invCand 11200 ys[r]!)
    else idTab 11200).flatten

meta def ptOf (els : Array (Array Nat)) (p : Nat) : Array (Array Nat) :=
  #[els.foldl (init := (Array.replicate 11200 0, 0)) (fun (a, j) t => (a.set! t[p]! j, j + 1)) |>.1]

meta def pE : Array (Array Nat) × Array (Array Nat) := pcSeq HarCD.recU 10

meta def nE : Array (Array Nat) := pE.1

meta def sqE : Array (Array Nat) := pE.2.map fun y => comp 11200 y y

meta def cjE : Array (Array Nat) := cjOf pE.2

meta def ptE : Array (Array Nat) := ptOf HarCD.recU 5

meta def pQ : Array (Array Nat) × Array (Array Nat) := pcSeq HarCD.recQ 7

meta def nQ : Array (Array Nat) := pQ.1

meta def sqQ : Array (Array Nat) := pQ.2.map fun y => comp 11200 y y

meta def cjQ : Array (Array Nat) := cjOf pQ.2

meta def ptQ : Array (Array Nat) := ptOf HarCD.recQ 2

end CFSG.KD.TwoHS.HarCN

#kfind CFSG.KD.TwoHS.TEP CFSG.KD.TwoHS.HarCD.recU CFSG.KD.TwoHS.HarCN.nE
#kfind CFSG.KD.TwoHS.TES CFSG.KD.TwoHS.HarCN.nE CFSG.KD.TwoHS.HarCD.recU
#kfind CFSG.KD.TwoHS.TEA CFSG.KD.TwoHS.HarCN.nE CFSG.KD.TwoHS.HarCN.sqE
#kfind CFSG.KD.TwoHS.TEB CFSG.KD.TwoHS.HarCN.nE CFSG.KD.TwoHS.HarCN.cjE
#kfind CFSG.KD.TwoHS.TEU CFSG.KD.TwoHS.HarCN.nE CFSG.KD.TwoHS.HarCD.gU
#kmisc_packarrs CFSG.KD.TwoHS.TEPP CFSG.KD.TwoHS.HarCN.ptE 14
#kfind CFSG.KD.TwoHS.TQP CFSG.KD.TwoHS.HarCD.recQ CFSG.KD.TwoHS.HarCN.nQ
#kfind CFSG.KD.TwoHS.TQS CFSG.KD.TwoHS.HarCN.nQ CFSG.KD.TwoHS.HarCD.recQ
#kfind CFSG.KD.TwoHS.TQA CFSG.KD.TwoHS.HarCN.nQ CFSG.KD.TwoHS.HarCN.sqQ
#kfind CFSG.KD.TwoHS.TQB CFSG.KD.TwoHS.HarCN.nQ CFSG.KD.TwoHS.HarCN.cjQ
#kfind CFSG.KD.TwoHS.TQU CFSG.KD.TwoHS.HarCN.nQ CFSG.KD.TwoHS.HarCD.gQ
#kmisc_packarrs CFSG.KD.TwoHS.TQPP CFSG.KD.TwoHS.HarCN.ptQ 14

end
