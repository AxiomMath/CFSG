module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVData
meta import Certificates.Kernel.HN1408.RecGen
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVData

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.ShVGen

open CFSG.EvenSporadicStandard.HNRecog
open CFSG.KD.HN1408.RecGen
open CFSG.Sporadic.SmallOddCore.Native (natArr)

meta def gD5 : Array (Array Nat) := gensM d5Words
meta def gD5I : Array (Array Nat) := gD5.map invM
meta def iD5 : Array (Array Nat) := idsOf gD5
meta def rD5 : Array (Array Nat) := recOf gD5
meta def cD5 : Array (Array Nat) := clOf gD5
meta def cI : Array (Array Nat) := (gensM (c0Word :: ckWords)).map invM

end CFSG.KD.HN1408.ShVGen

end

set_option maxRecDepth 400000

#kmulh CFSG.KD.HN1408.ShVD5 1408 11 CFSG.KD.HN1408.ShVGen.iD5 CFSG.KD.HN1408.ShVGen.gD5
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.ShVD5Cl CFSG.KD.HN1408.ShVGen.rD5 CFSG.KD.HN1408.ShVGen.cD5
#kmisc_packarrs CFSG.KD.HN1408.ShVD5I CFSG.KD.HN1408.ShVGen.gD5I 11
#kmisc_packarrs CFSG.KD.HN1408.ShVCI CFSG.KD.HN1408.ShVGen.cI 11
