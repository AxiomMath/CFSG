module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarCOdd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarCOdd
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
meta import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS.HarCD

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 11200

meta def gU : Array (Array Nat) := (harU.map natArr).toArray

meta def idsU : Array (Array Nat) := Array.replicate gU.size idM

meta def giU : Array (Array Nat) := gU.map (CFSG.Monster.B.Co2.Native.invCand 11200)

meta def recU : Array (Array Nat) := (bfs (fun j t => conjTab 11200 idM gU[j]! t) gU.size idM 2000).tabs

meta def clU : Array (Array Nat) := (recU.map fun x => (gU ++ giU).map fun g => comp 11200 x g).flatten

meta def gQ : Array (Array Nat) := ((harCQ ()).map natArr).toArray

meta def idsQ : Array (Array Nat) := Array.replicate gQ.size idM

meta def giQ : Array (Array Nat) := gQ.map (CFSG.Monster.B.Co2.Native.invCand 11200)

meta def recQ : Array (Array Nat) := (bfs (fun j t => conjTab 11200 idM gQ[j]! t) gQ.size idM 400).tabs

meta def clQ : Array (Array Nat) := (recQ.map fun x => (gQ ++ giQ).map fun g => comp 11200 x g).flatten

meta def csM : Array (Array Nat) := ((harCGens ()).map natArr).toArray

meta def csiM : Array (Array Nat) := csM.map (CFSG.Monster.B.Co2.Native.invCand 11200)

meta def nqM : Array (Array Nat) :=
  (recQ.map fun x => (List.range csM.size).toArray.map fun j =>
    comp 11200 (comp 11200 csM[j]! x) csiM[j]!).flatten

meta def rootM : Array (Array Nat) := #[natArr (tU harCRoot)]

end CFSG.KD.TwoHS.HarCD

#kmulh CFSG.KD.TwoHS.TE 11200 14 CFSG.KD.TwoHS.HarCD.idsU CFSG.KD.TwoHS.HarCD.gU
  CFSG.KD.TwoHS.HarCD.idM 2000
#kmisc_packarrs CFSG.KD.TwoHS.TEI CFSG.KD.TwoHS.HarCD.giU 14
#kfind CFSG.KD.TwoHS.TECl CFSG.KD.TwoHS.HarCD.recU CFSG.KD.TwoHS.HarCD.clU
#kmulh CFSG.KD.TwoHS.TQ 11200 14 CFSG.KD.TwoHS.HarCD.idsQ CFSG.KD.TwoHS.HarCD.gQ
  CFSG.KD.TwoHS.HarCD.idM 400
#kmisc_packarrs CFSG.KD.TwoHS.TQI CFSG.KD.TwoHS.HarCD.giQ 14
#kfind CFSG.KD.TwoHS.TQCl CFSG.KD.TwoHS.HarCD.recQ CFSG.KD.TwoHS.HarCD.clQ
#kmisc_packarrs CFSG.KD.TwoHS.TCG CFSG.KD.TwoHS.HarCD.csM 14
#kmisc_packarrs CFSG.KD.TwoHS.TCGI CFSG.KD.TwoHS.HarCD.csiM 14
#kfind CFSG.KD.TwoHS.TQN CFSG.KD.TwoHS.HarCD.recQ CFSG.KD.TwoHS.HarCD.nqM
#kfind CFSG.KD.TwoHS.TQR CFSG.KD.TwoHS.HarCD.recQ CFSG.KD.TwoHS.HarCD.rootM

end
