module

public import Certificates.Kernel.HN1408.W441872Defs
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalQT.PEnumD
meta import Certificates.Kernel.HN1408.W441872Defs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.WitCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockCheck
public import Certificates.Kernel.HN1408.Y442202Inst
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockCheck
meta import Certificates.Kernel.HN1408.Y442202Inst

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.W441872M

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.CompatModel

meta def tabN (t : CFSG.Sporadic.Th.Native.Table) : Array Nat := t.map UInt32.toNat
meta def idM : Array Nat := idTab 1408
meta def wM (w : List Nat) : Array Nat := tabN (tabW w)
meta def mulM (p q : Array Nat) : Array Nat := comp 1408 p q
meta def genW : Array (Array Nat) := (witSylow.map wM).toArray
meta def ids5 : Array (Array Nat) := Array.replicate 5 idM
meta def recW : Array (Array Nat) :=
  (bfs (fun j t => conjTab 1408 genW[j]! idM t) genW.size idM 4096).tabs
meta def vTabs : Array (Array Nat) := (CFSG.KD.HN1408.W441872.vWords.map wM).toArray

meta def tA : Array Nat := wM wordA
meta def tB : Array Nat := wM wordB
meta def tAB : Array Nat := mulM tA tB

meta def covM (x : Array Nat) : Nat :=
  if mulM x x == idM && x != idM && x != tA && x != tB && x != tAB then
    (vTabs.findIdx? fun v => mulM v x == mulM x v).getD 16
  else 16

meta def cvW : Array Nat := recW.map covM

end CFSG.KD.HN1408.W441872M

open CFSG.KD.HN1408.W441872M in
#kmulh CFSG.KD.HN1408.W441872.SW 1408 11 genW ids5 idM 4096
open CFSG.KD.HN1408.W441872M in
#kmisc_packarrs CFSG.KD.HN1408.W441872.V vTabs 11
open CFSG.KD.HN1408.W441872M in
#krows32 CFSG.KD.HN1408.W441872.CV cvW
