module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKData
meta import Certificates.Kernel.HN1408.RecGen
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKData

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TKGen

open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.RecGen
open CFSG.Sporadic.SmallOddCore.Native (natArr)

meta def cmp26773 (p q : Array Nat) : Array Nat := q.map fun x => p[x]!

meta def gQ : Array (Array Nat) := gensM qWordsK
meta def gQI : Array (Array Nat) := gQ.map invM
meta def iQ : Array (Array Nat) := idsOf gQ
meta def rQ : Array (Array Nat) := recOf gQ
meta def cQ : Array (Array Nat) := clOf gQ
meta def gE : Array (Array Nat) := gensM eWordsK
meta def gEI : Array (Array Nat) := gE.map invM
meta def iE : Array (Array Nat) := idsOf gE
meta def rE : Array (Array Nat) := recOf gE
meta def cE : Array (Array Nat) := clOf gE
meta def gZ : Array (Array Nat) := gensM zcWordsK
meta def gZI : Array (Array Nat) := gZ.map invM
meta def iZ : Array (Array Nat) := idsOf gZ
meta def rZ : Array (Array Nat) := recOf gZ
meta def cZ : Array (Array Nat) := clOf gZ

meta def tc : Array Nat := natArr (tabW cWordK)

meta def wC : Array (Array Nat) := posOf rQ #[tc] ++ posOf rZ #[tc]
meta def wP : Array (Array Nat) := posOf rQ gE

meta def ncOf (gs : Array (Array Nat)) (s : Array Nat) : Option Nat :=
  (List.range gs.size).find? fun j => cmp26773 s gs[j]! != cmp26773 gs[j]! s

meta def wQ : Array (Array Nat) :=
  rQ.map fun s => #[(ncOf gQ s).getD (if s == idM then 4 else if s == tc then 5 else 6)]

end CFSG.KD.HN1408.TKGen

end

set_option maxRecDepth 400000

#kmulh CFSG.KD.HN1408.TKQ 1408 11 CFSG.KD.HN1408.TKGen.iQ CFSG.KD.HN1408.TKGen.gQ
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.TKQCl CFSG.KD.HN1408.TKGen.rQ CFSG.KD.HN1408.TKGen.cQ
#kmisc_packarrs CFSG.KD.HN1408.TKQI CFSG.KD.HN1408.TKGen.gQI 11
#kmulh CFSG.KD.HN1408.TKE 1408 11 CFSG.KD.HN1408.TKGen.iE CFSG.KD.HN1408.TKGen.gE
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.TKECl CFSG.KD.HN1408.TKGen.rE CFSG.KD.HN1408.TKGen.cE
#kmisc_packarrs CFSG.KD.HN1408.TKEI CFSG.KD.HN1408.TKGen.gEI 11
#kmulh CFSG.KD.HN1408.TKZ 1408 11 CFSG.KD.HN1408.TKGen.iZ CFSG.KD.HN1408.TKGen.gZ
  CFSG.KD.HN1408.RecGen.idM 100000
#kfind CFSG.KD.HN1408.TKZCl CFSG.KD.HN1408.TKGen.rZ CFSG.KD.HN1408.TKGen.cZ
#kmisc_packarrs CFSG.KD.HN1408.TKZI CFSG.KD.HN1408.TKGen.gZI 11

#kmisc_packarrs CFSG.KD.HN1408.TKC CFSG.KD.HN1408.TKGen.wC 32
#kmisc_packarrs CFSG.KD.HN1408.TKP CFSG.KD.HN1408.TKGen.wP 32
#kmisc_packarrs CFSG.KD.HN1408.TKQW CFSG.KD.HN1408.TKGen.wQ 32
