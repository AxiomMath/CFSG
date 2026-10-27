module

public import Certificates.Kernel.HN1408.Words
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.BaseMask
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.E64Data
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.AData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.SylSM

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel

meta def tabN (t : CFSG.Sporadic.Th.Native.Table) : Array Nat := t.map UInt32.toNat
meta def idM : Array Nat := idTab 1408
meta def wM (w : List Nat) : Array Nat := tabN (tabW w)
meta def genM : Array (Array Nat) := (sWords.map wM).toArray
meta def idsM : Array (Array Nat) := Array.replicate 5 idM
meta def recM : Array (Array Nat) :=
  (bfs (fun j t => conjTab 1408 genM[j]! idsM[j]! t) 5 idM 4096).tabs
meta def keyM (t : Array Nat) : Nat := t[2]! * 1408 + t[0]!
meta def sortM : Array (Array Nat) := recM.qsort fun a b => keyM a < keyM b
meta def isInvM (t : Array Nat) : Bool := comp 1408 t t == idM && t != idM
meta def ivM : Array (Array Nat) := recM.filter isInvM
meta def dblM (gs : List (Array Nat)) : Array (Array Nat) :=
  gs.foldl (fun X g => X ++ X.map fun x => comp 1408 x g) #[idM]
meta def esM : Array (Array Nat) := (subgroupList 100000 sWords).map tabN
meta def extGens (xs : List Nat) : List (Array Nat) :=
  wM wordA :: wM wordZ :: xs.map fun i => esM[i]!
meta def membersM : List (List (Array Nat)) :=
  [[]].map extGens ++ e64Ext3.map extGens ++ e64Ext4.map extGens ++ e64Ext5.map extGens ++
    e64Ext6.map extGens
meta def famM : Array (Array Nat) := (membersM.map dblM).toArray.flatten
meta def famGensM : Array (Array Nat) := membersM.flatten.toArray
meta def gdM : Array (Array Nat) :=
  famGensM.foldl (fun D g => if D.contains g then D else D.push g) #[]
meta def commM (s g : Array Nat) : Bool := comp 1408 s g == comp 1408 g s
meta def cmM : Array (Array Nat) := gdM.map fun g =>
  recM.map fun s => if isInvM s && commM s g then 1 else 0
meta def aRecM : Array (Array Nat) := dblM (uWords.map wM)
meta def yM : Array Nat := genM[4]!
meta def yArrM : Array (Array Nat) := #[yM]
meta def cRecM : Array (Array Nat) := aRecM.map fun t => comp 1408 (comp 1408 yM t) (invTab 1408 yM)

end CFSG.KD.HN1408.SylSM

open CFSG.KD.HN1408.SylSM in
#kmulh CFSG.KD.HN1408.SylS 1408 11 genM idsM idM 4096
open CFSG.KD.HN1408.SylSM in
#kfind CFSG.KD.HN1408.SylS.KS recM sortM
open CFSG.KD.HN1408.SylSM in
#kfind CFSG.KD.HN1408.SylS.KSI sortM recM
open CFSG.KD.HN1408.SylSM in
#kfind CFSG.KD.HN1408.SylS.IV recM ivM
open CFSG.KD.HN1408.SylSM in
#kfind CFSG.KD.HN1408.SylS.FM recM famM
open CFSG.KD.HN1408.SylSM in
#kfind CFSG.KD.HN1408.SylS.FG gdM famGensM
open CFSG.KD.HN1408.SylSM in
#kfind CFSG.KD.HN1408.SylS.GD recM gdM
open CFSG.KD.HN1408.SylSM in
#kmisc_packarrs CFSG.KD.HN1408.SylS.CM cmM 1
open CFSG.KD.HN1408.SylSM in
#kfind CFSG.KD.HN1408.SylS.FA recM aRecM
open CFSG.KD.HN1408.SylSM in
#kfind CFSG.KD.HN1408.SylS.FC recM cRecM
open CFSG.KD.HN1408.SylSM in
#kfind CFSG.KD.HN1408.SylS.Y recM yArrM

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.BaseMask

@[expose] noncomputable def nIV : Nat := 303

@[expose] noncomputable def nGD : Nat := 77

@[expose] noncomputable def ivMask : Nat := maskK SylS.IV 0 nIV

@[expose] noncomputable def slS (s : Nat) : Bool :=
  penumSlK 1408 11 (mask 11) (Nat.mul 1408 11) false SylS.G SylS.GI 5 SylS.cnt SylS.T SylS.PL
    SylS.POS SylS.SRT SylS.SRI (Nat.mul 256 s) 256

end CFSG.KD.HN1408

end
