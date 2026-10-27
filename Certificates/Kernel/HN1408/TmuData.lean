module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Letters
meta import Certificates.Kernel.HN1408.RecGen
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Letters

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TmGen

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5
open CFSG.KD.HN1408.RecGen
open CFSG.Sporadic.SmallOddCore.Native (natArr)

meta def t0 : Array Nat := natArr (tabW wordAZ)

meta def gT0 : Array (Array Nat) := gensM (tWords 0)
meta def gT0I : Array (Array Nat) := gT0.map invM
meta def iT0 : Array (Array Nat) := idsOf gT0
meta def rT0 : Array (Array Nat) := recOf gT0
meta def cT0 : Array (Array Nat) := clOf gT0
meta def gM0 : Array (Array Nat) := gensM (mWords 0)
meta def gM0I : Array (Array Nat) := gM0.map invM
meta def iM0 : Array (Array Nat) := idsOf gM0
meta def rM0 : Array (Array Nat) := recOf gM0
meta def cM0 : Array (Array Nat) := clOf gM0
meta def q0 : Array (Array Nat) := #[t0, natArr (tabW (uWord 0))] ++ gM0

meta def gT1 : Array (Array Nat) := gensM (tWords 1)
meta def gT1I : Array (Array Nat) := gT1.map invM
meta def iT1 : Array (Array Nat) := idsOf gT1
meta def rT1 : Array (Array Nat) := recOf gT1
meta def cT1 : Array (Array Nat) := clOf gT1
meta def gM1 : Array (Array Nat) := gensM (mWords 1)
meta def gM1I : Array (Array Nat) := gM1.map invM
meta def iM1 : Array (Array Nat) := idsOf gM1
meta def rM1 : Array (Array Nat) := recOf gM1
meta def cM1 : Array (Array Nat) := clOf gM1
meta def q1 : Array (Array Nat) := #[t0, natArr (tabW (uWord 1))] ++ gM1

end CFSG.KD.HN1408.TmGen

end

set_option maxRecDepth 400000

#kmulh CFSG.KD.HN1408.TmT0 1408 11 CFSG.KD.HN1408.TmGen.iT0 CFSG.KD.HN1408.TmGen.gT0
  CFSG.KD.HN1408.RecGen.idM 1000
#kfind CFSG.KD.HN1408.TmT0Cl CFSG.KD.HN1408.TmGen.rT0 CFSG.KD.HN1408.TmGen.cT0
#kmisc_packarrs CFSG.KD.HN1408.TmT0I CFSG.KD.HN1408.TmGen.gT0I 11
#kmulh CFSG.KD.HN1408.TmM0 1408 11 CFSG.KD.HN1408.TmGen.iM0 CFSG.KD.HN1408.TmGen.gM0
  CFSG.KD.HN1408.RecGen.idM 1000
#kfind CFSG.KD.HN1408.TmM0Cl CFSG.KD.HN1408.TmGen.rM0 CFSG.KD.HN1408.TmGen.cM0
#kmisc_packarrs CFSG.KD.HN1408.TmM0I CFSG.KD.HN1408.TmGen.gM0I 11
#kfind CFSG.KD.HN1408.TmP0 CFSG.KD.HN1408.TmGen.rT0 CFSG.KD.HN1408.TmGen.q0

#kmulh CFSG.KD.HN1408.TmT1 1408 11 CFSG.KD.HN1408.TmGen.iT1 CFSG.KD.HN1408.TmGen.gT1
  CFSG.KD.HN1408.RecGen.idM 1000
#kfind CFSG.KD.HN1408.TmT1Cl CFSG.KD.HN1408.TmGen.rT1 CFSG.KD.HN1408.TmGen.cT1
#kmisc_packarrs CFSG.KD.HN1408.TmT1I CFSG.KD.HN1408.TmGen.gT1I 11
#kmulh CFSG.KD.HN1408.TmM1 1408 11 CFSG.KD.HN1408.TmGen.iM1 CFSG.KD.HN1408.TmGen.gM1
  CFSG.KD.HN1408.RecGen.idM 1000
#kfind CFSG.KD.HN1408.TmM1Cl CFSG.KD.HN1408.TmGen.rM1 CFSG.KD.HN1408.TmGen.cM1
#kmisc_packarrs CFSG.KD.HN1408.TmM1I CFSG.KD.HN1408.TmGen.gM1I 11
#kfind CFSG.KD.HN1408.TmP1 CFSG.KD.HN1408.TmGen.rT1 CFSG.KD.HN1408.TmGen.q1
