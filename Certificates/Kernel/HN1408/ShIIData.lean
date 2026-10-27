module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIIData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixData
meta import Certificates.Kernel.HN1408.RecGen
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIIData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixData

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.ShIIGen

open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.RecGen CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore.Native (natArr)

meta def gY3 : Array (Array Nat) := gensM y3Words
meta def gY3I : Array (Array Nat) := gY3.map invM
meta def iY3 : Array (Array Nat) := idsOf gY3
meta def rY3 : Array (Array Nat) := recOf gY3
meta def cY3 : Array (Array Nat) := clOf gY3
meta def gN3 : Array (Array Nat) := gensM n3Words
meta def gN3I : Array (Array Nat) := gN3.map invM
meta def iN3 : Array (Array Nat) := idsOf gN3
meta def rN3 : Array (Array Nat) := recOf gN3
meta def cN3 : Array (Array Nat) := clOf gN3
meta def gV3 : Array (Array Nat) := gensM v3Words
meta def gV3I : Array (Array Nat) := gV3.map invM
meta def iV3 : Array (Array Nat) := idsOf gV3
meta def rV3 : Array (Array Nat) := recOf gV3
meta def cV3 : Array (Array Nat) := clOf gV3
meta def gA3 : Array (Array Nat) := gensM a3Words
meta def gA3I : Array (Array Nat) := gA3.map invM
meta def iA3 : Array (Array Nat) := idsOf gA3
meta def rA3 : Array (Array Nat) := recOf gA3
meta def cA3 : Array (Array Nat) := clOf gA3
meta def gN5 : Array (Array Nat) := gensM n5Words
meta def gN5I : Array (Array Nat) := gN5.map invM
meta def iN5 : Array (Array Nat) := idsOf gN5
meta def rN5 : Array (Array Nat) := recOf gN5
meta def cN5 : Array (Array Nat) := clOf gN5
meta def gS5 : Array (Array Nat) := gensM s5Words
meta def gS5I : Array (Array Nat) := gS5.map invM
meta def iS5 : Array (Array Nat) := idsOf gS5
meta def rS5 : Array (Array Nat) := recOf gS5
meta def cS5 : Array (Array Nat) := clOf gS5
meta def gB5 : Array (Array Nat) := gensM b5Words
meta def gB5I : Array (Array Nat) := gB5.map invM
meta def iB5 : Array (Array Nat) := idsOf gB5
meta def rB5 : Array (Array Nat) := recOf gB5
meta def cB5 : Array (Array Nat) := clOf gB5
meta def gY5 : Array (Array Nat) := gensM y5Words
meta def gY5I : Array (Array Nat) := gY5.map invM
meta def iY5 : Array (Array Nat) := idsOf gY5
meta def rY5 : Array (Array Nat) := recOf gY5
meta def cY5 : Array (Array Nat) := clOf gY5

meta def pY3 : Array (Array Nat) := gN3
meta def pN3 : Array (Array Nat) := gV3 ++ gA3
meta def gC5 : Array (Array Nat) := gensM fix5A.cent
meta def gC5I : Array (Array Nat) := gC5.map invM
meta def pN5 : Array (Array Nat) :=
  ((List.range gC5.size).toArray.map fun c => gN5.map fun n =>
    #[conjTab 1408 gC5[c]! gC5I[c]! n, conjTab 1408 gC5I[c]! gC5[c]! n]).flatten.flatten
meta def pY5 : Array (Array Nat) :=
  #[natArr (tabW wordA), natArr (tabW u5Word), natArr (tabW v5Word)]
meta def gUVI : Array (Array Nat) := (gensM [u5Word, v5Word]).map invM

meta def blkM : Array (Array Nat) := #[blkOfString blkStrA3, blkOfString blkStrY5]
meta def labM (L : List CFSG.Sporadic.Th.Native.Table) : Array (Array Nat) := L.toArray.map natArr
meta def lA : Array (Array Nat) := labM labsA3
meta def lY : Array (Array Nat) := labM labsY5
meta def lAJ : Array (Array Nat) := lA.map (CFSG.Monster.B.Co2.Native.invCand 5)
meta def lYJ : Array (Array Nat) := lY.map (CFSG.Monster.B.Co2.Native.invCand 5)
meta def id5 : Array Nat := idTab 5
meta def ids5 : Array (Array Nat) := Array.replicate 2 id5
meta def rlA : Array (Array Nat) := recOfN 5 lA
meta def clA : Array (Array Nat) := clOfN 5 lA
meta def rlY : Array (Array Nat) := recOfN 5 lY
meta def clY : Array (Array Nat) := clOfN 5 lY

end CFSG.KD.HN1408.ShIIGen

end

set_option maxRecDepth 400000

#kmulh CFSG.KD.HN1408.ShIIY3 1408 11 CFSG.KD.HN1408.ShIIGen.iY3 CFSG.KD.HN1408.ShIIGen.gY3
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.ShIIY3Cl CFSG.KD.HN1408.ShIIGen.rY3 CFSG.KD.HN1408.ShIIGen.cY3
#kmisc_packarrs CFSG.KD.HN1408.ShIIY3I CFSG.KD.HN1408.ShIIGen.gY3I 11
#kmulh CFSG.KD.HN1408.ShIIN3 1408 11 CFSG.KD.HN1408.ShIIGen.iN3 CFSG.KD.HN1408.ShIIGen.gN3
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.ShIIN3Cl CFSG.KD.HN1408.ShIIGen.rN3 CFSG.KD.HN1408.ShIIGen.cN3
#kmisc_packarrs CFSG.KD.HN1408.ShIIN3I CFSG.KD.HN1408.ShIIGen.gN3I 11
#kmulh CFSG.KD.HN1408.ShIIV3 1408 11 CFSG.KD.HN1408.ShIIGen.iV3 CFSG.KD.HN1408.ShIIGen.gV3
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.ShIIV3Cl CFSG.KD.HN1408.ShIIGen.rV3 CFSG.KD.HN1408.ShIIGen.cV3
#kmisc_packarrs CFSG.KD.HN1408.ShIIV3I CFSG.KD.HN1408.ShIIGen.gV3I 11
#kmulh CFSG.KD.HN1408.ShIIA3 1408 11 CFSG.KD.HN1408.ShIIGen.iA3 CFSG.KD.HN1408.ShIIGen.gA3
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.ShIIA3Cl CFSG.KD.HN1408.ShIIGen.rA3 CFSG.KD.HN1408.ShIIGen.cA3
#kmisc_packarrs CFSG.KD.HN1408.ShIIA3I CFSG.KD.HN1408.ShIIGen.gA3I 11
#kmulh CFSG.KD.HN1408.ShIIN5 1408 11 CFSG.KD.HN1408.ShIIGen.iN5 CFSG.KD.HN1408.ShIIGen.gN5
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.ShIIN5Cl CFSG.KD.HN1408.ShIIGen.rN5 CFSG.KD.HN1408.ShIIGen.cN5
#kmisc_packarrs CFSG.KD.HN1408.ShIIN5I CFSG.KD.HN1408.ShIIGen.gN5I 11
#kmulh CFSG.KD.HN1408.ShIIS5 1408 11 CFSG.KD.HN1408.ShIIGen.iS5 CFSG.KD.HN1408.ShIIGen.gS5
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.ShIIS5Cl CFSG.KD.HN1408.ShIIGen.rS5 CFSG.KD.HN1408.ShIIGen.cS5
#kmisc_packarrs CFSG.KD.HN1408.ShIIS5I CFSG.KD.HN1408.ShIIGen.gS5I 11
#kmulh CFSG.KD.HN1408.ShIIB5 1408 11 CFSG.KD.HN1408.ShIIGen.iB5 CFSG.KD.HN1408.ShIIGen.gB5
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.ShIIB5Cl CFSG.KD.HN1408.ShIIGen.rB5 CFSG.KD.HN1408.ShIIGen.cB5
#kmisc_packarrs CFSG.KD.HN1408.ShIIB5I CFSG.KD.HN1408.ShIIGen.gB5I 11
#kmulh CFSG.KD.HN1408.ShIIY5 1408 11 CFSG.KD.HN1408.ShIIGen.iY5 CFSG.KD.HN1408.ShIIGen.gY5
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.ShIIY5Cl CFSG.KD.HN1408.ShIIGen.rY5 CFSG.KD.HN1408.ShIIGen.cY5
#kmisc_packarrs CFSG.KD.HN1408.ShIIY5I CFSG.KD.HN1408.ShIIGen.gY5I 11

#kfind CFSG.KD.HN1408.ShIIPY3 CFSG.KD.HN1408.ShIIGen.rY3 CFSG.KD.HN1408.ShIIGen.pY3
#kfind CFSG.KD.HN1408.ShIIPN3 CFSG.KD.HN1408.ShIIGen.rN3 CFSG.KD.HN1408.ShIIGen.pN3
#kfind CFSG.KD.HN1408.ShIIPN5 CFSG.KD.HN1408.ShIIGen.rN5 CFSG.KD.HN1408.ShIIGen.pN5
#kfind CFSG.KD.HN1408.ShIIPY5 CFSG.KD.HN1408.ShIIGen.rY5 CFSG.KD.HN1408.ShIIGen.pY5
#kmisc_packarrs CFSG.KD.HN1408.ShIIC5I CFSG.KD.HN1408.ShIIGen.gC5I 11
#kmisc_packarrs CFSG.KD.HN1408.ShIIUVI CFSG.KD.HN1408.ShIIGen.gUVI 11

#ks_chars CFSG.KD.HN1408.ShIIBA CFSG.EvenSporadicStandard.HNRecog.blkStrA3
#ks_chars CFSG.KD.HN1408.ShIIBY CFSG.EvenSporadicStandard.HNRecog.blkStrY5
#kmisc_packarrs CFSG.KD.HN1408.ShIIB CFSG.KD.HN1408.ShIIGen.blkM 4

#kmulh CFSG.KD.HN1408.ShIILA 5 4 CFSG.KD.HN1408.ShIIGen.ids5 CFSG.KD.HN1408.ShIIGen.lA
  CFSG.KD.HN1408.ShIIGen.id5 100000
#kfind CFSG.KD.HN1408.ShIILACl CFSG.KD.HN1408.ShIIGen.rlA CFSG.KD.HN1408.ShIIGen.clA
#kmisc_packarrs CFSG.KD.HN1408.ShIILAJ CFSG.KD.HN1408.ShIIGen.lAJ 4
#kmulh CFSG.KD.HN1408.ShIILY 5 4 CFSG.KD.HN1408.ShIIGen.ids5 CFSG.KD.HN1408.ShIIGen.lY
  CFSG.KD.HN1408.ShIIGen.id5 100000
#kfind CFSG.KD.HN1408.ShIILYCl CFSG.KD.HN1408.ShIIGen.rlY CFSG.KD.HN1408.ShIIGen.clY
#kmisc_packarrs CFSG.KD.HN1408.ShIILYJ CFSG.KD.HN1408.ShIIGen.lYJ 4
