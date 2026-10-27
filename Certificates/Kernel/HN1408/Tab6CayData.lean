module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData
meta import Certificates.Kernel.HN1408.RecGen
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Data
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tab6Gen

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model
open CFSG.KD.HN1408.RecGen

meta def g2 : Array (Array Nat) := gensM (tab6Row2.stabWords classaz.centGens)
meta def g2I : Array (Array Nat) := g2.map invM
meta def i2 : Array (Array Nat) := idsOf g2
meta def r2 : Array (Array Nat) := recOf g2
meta def c2 : Array (Array Nat) := clOf g2
meta def g4 : Array (Array Nat) := gensM (tab6Row4.stabWords classaz.centGens)
meta def g4I : Array (Array Nat) := g4.map invM
meta def i4 : Array (Array Nat) := idsOf g4
meta def r4 : Array (Array Nat) := recOf g4
meta def c4 : Array (Array Nat) := clOf g4
meta def g6 : Array (Array Nat) := gensM (tab6Row6.stabWords classaz.centGens)
meta def g6I : Array (Array Nat) := g6.map invM
meta def i6 : Array (Array Nat) := idsOf g6
meta def r6 : Array (Array Nat) := recOf g6
meta def c6 : Array (Array Nat) := clOf g6
meta def g7 : Array (Array Nat) := gensM (tab6Row7.stabWords classaz.centGens)
meta def g7I : Array (Array Nat) := g7.map invM
meta def i7 : Array (Array Nat) := idsOf g7
meta def r7 : Array (Array Nat) := recOf g7
meta def c7 : Array (Array Nat) := clOf g7

end CFSG.KD.HN1408.Tab6Gen

end

set_option maxRecDepth 400000

#kmulh CFSG.KD.HN1408.Tab6S2 1408 11 CFSG.KD.HN1408.Tab6Gen.i2 CFSG.KD.HN1408.Tab6Gen.g2
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.Tab6S2Cl CFSG.KD.HN1408.Tab6Gen.r2 CFSG.KD.HN1408.Tab6Gen.c2
#kmisc_packarrs CFSG.KD.HN1408.Tab6S2I CFSG.KD.HN1408.Tab6Gen.g2I 11
#kmulh CFSG.KD.HN1408.Tab6S4 1408 11 CFSG.KD.HN1408.Tab6Gen.i4 CFSG.KD.HN1408.Tab6Gen.g4
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.Tab6S4Cl CFSG.KD.HN1408.Tab6Gen.r4 CFSG.KD.HN1408.Tab6Gen.c4
#kmisc_packarrs CFSG.KD.HN1408.Tab6S4I CFSG.KD.HN1408.Tab6Gen.g4I 11
#kmulh CFSG.KD.HN1408.Tab6S6 1408 11 CFSG.KD.HN1408.Tab6Gen.i6 CFSG.KD.HN1408.Tab6Gen.g6
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.Tab6S6Cl CFSG.KD.HN1408.Tab6Gen.r6 CFSG.KD.HN1408.Tab6Gen.c6
#kmisc_packarrs CFSG.KD.HN1408.Tab6S6I CFSG.KD.HN1408.Tab6Gen.g6I 11
#kmulh CFSG.KD.HN1408.Tab6S7 1408 11 CFSG.KD.HN1408.Tab6Gen.i7 CFSG.KD.HN1408.Tab6Gen.g7
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.Tab6S7Cl CFSG.KD.HN1408.Tab6Gen.r7 CFSG.KD.HN1408.Tab6Gen.c7
#kmisc_packarrs CFSG.KD.HN1408.Tab6S7I CFSG.KD.HN1408.Tab6Gen.g7I 11
