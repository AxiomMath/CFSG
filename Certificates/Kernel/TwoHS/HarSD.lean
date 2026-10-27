module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS.HarSD

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore

meta def idM : Array Nat := idTab 3850

meta def gD : Array (Array Nat) := (harSCgens.map natArr).toArray

meta def idsD : Array (Array Nat) := Array.replicate gD.size idM

meta def giD : Array (Array Nat) := gD.map (CFSG.Monster.B.Co2.Native.invCand 3850)

meta def recD : Array (Array Nat) := (bfs (fun j t => conjTab 3850 idM gD[j]! t) gD.size idM 200).tabs

meta def clD : Array (Array Nat) := (recD.map fun x => (gD ++ giD).map fun g => comp 3850 x g).flatten

meta def sM : Array (Array Nat) := (hsSylowGenTbls.map natArr).toArray

meta def siM : Array (Array Nat) := sM.map (CFSG.Monster.B.Co2.Native.invCand 3850)

meta def nM : Array (Array Nat) :=
  (recD.map fun x => (List.range sM.size).toArray.map fun j =>
    comp 3850 (comp 3850 sM[j]! x) siM[j]!).flatten

meta def mM : Array (Array Nat) :=
  ((List.range sM.size).toArray.map fun a => (List.range sM.size).toArray.map fun b =>
    comp 3850 (comp 3850 sM[a]! sM[b]!) (comp 3850 siM[a]! siM[b]!)).flatten

end CFSG.KD.TwoHS.HarSD

#kmulh CFSG.KD.TwoHS.SD 3850 12 CFSG.KD.TwoHS.HarSD.idsD CFSG.KD.TwoHS.HarSD.gD
  CFSG.KD.TwoHS.HarSD.idM 200
#kmisc_packarrs CFSG.KD.TwoHS.SDI CFSG.KD.TwoHS.HarSD.giD 12
#kfind CFSG.KD.TwoHS.SDCl CFSG.KD.TwoHS.HarSD.recD CFSG.KD.TwoHS.HarSD.clD
#kfind CFSG.KD.TwoHS.SDN CFSG.KD.TwoHS.HarSD.recD CFSG.KD.TwoHS.HarSD.nM
#kfind CFSG.KD.TwoHS.SDM CFSG.KD.TwoHS.HarSD.recD CFSG.KD.TwoHS.HarSD.mM

end
