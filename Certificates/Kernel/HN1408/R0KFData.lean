module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.FData
meta import Certificates.Kernel.HN1408.RecGen
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.FData

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.R0KFGen

open CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.KD.HN1408.RecGen

meta def gF : Array (Array Nat) := gensM fWords
meta def gFI : Array (Array Nat) := gF.map invM
meta def iF : Array (Array Nat) := idsOf gF
meta def rF : Array (Array Nat) := recOf gF
meta def cF : Array (Array Nat) := clOf gF

end CFSG.KD.HN1408.R0KFGen

end

set_option maxRecDepth 400000

#kmulh CFSG.KD.HN1408.R0KF 1408 11 CFSG.KD.HN1408.R0KFGen.iF CFSG.KD.HN1408.R0KFGen.gF
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.R0KFCl CFSG.KD.HN1408.R0KFGen.rF CFSG.KD.HN1408.R0KFGen.cF
#kmisc_packarrs CFSG.KD.HN1408.R0KFI CFSG.KD.HN1408.R0KFGen.gFI 11
