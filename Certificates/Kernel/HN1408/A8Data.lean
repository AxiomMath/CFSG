module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.A8LabelCheck
meta import Certificates.Kernel.HN1408.RecGen
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.A8LabelCheck

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.A8Gen

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model
open CFSG.KD.HN1408.RecGen
open CFSG.Sporadic.SmallOddCore.Native (natArr)

meta def gk : Array (Array Nat) := gensM classb.centGens
meta def gkI : Array (Array Nat) := gk.map invM
meta def u0 : Array Nat := natArr (tabW a8W0)
meta def gs : Array (Array Nat) := gensM (a8Row.stabWords classb.centGens)
meta def ids : Array (Array Nat) := idsOf gs

end CFSG.KD.HN1408.A8Gen

end

set_option maxRecDepth 400000

#kmulh CFSG.KD.HN1408.A8O 1408 11 CFSG.KD.HN1408.A8Gen.gk CFSG.KD.HN1408.A8Gen.gkI
  CFSG.KD.HN1408.A8Gen.u0 100000
#kmulh CFSG.KD.HN1408.A8S 1408 11 CFSG.KD.HN1408.A8Gen.ids CFSG.KD.HN1408.A8Gen.gs
  CFSG.KD.HN1408.RecGen.idM 100000
