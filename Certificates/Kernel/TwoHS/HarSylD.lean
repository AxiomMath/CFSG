module

public import Certificates.Kernel.TwoHS.HarCD
public import Certificates.Kernel.LocalQT.PEnumD
meta import Certificates.Kernel.TwoHS.HarCD
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS.HarSylD

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def gC : Array (Array Nat) := (harCgens.map natArr).toArray

meta def gW : Array (Array Nat) := (harWgens.map natArr).toArray

meta def eC : Enum := bfs (fun j t => conjTab 11200 HarCD.idM gC[j]! t) gC.size HarCD.idM 400

meta def eW : Enum := bfs (fun j t => conjTab 11200 HarCD.idM gW[j]! t) gW.size HarCD.idM 800

meta def tC : Array (Array Nat) := eC.tabs

meta def tW : Array (Array Nat) := eW.tabs

meta def parC : Array Nat := eC.par

meta def labC : Array Nat := eC.lab

meta def parW : Array Nat := eW.par

meta def labW : Array Nat := eW.lab

meta def invOf (ts : Array (Array Nat)) : Array Nat :=
  let idx := indexOf ts
  HarCD.recU.map fun t => idx.getD t 4294967295

meta def invC : Array Nat := invOf tC

meta def invW : Array Nat := invOf tW

end CFSG.KD.TwoHS.HarSylD

#kfind CFSG.KD.TwoHS.CPos CFSG.KD.TwoHS.HarCD.recU CFSG.KD.TwoHS.HarSylD.tC
#kfind CFSG.KD.TwoHS.WPos CFSG.KD.TwoHS.HarCD.recU CFSG.KD.TwoHS.HarSylD.tW
#krows32 CFSG.KD.TwoHS.CPar CFSG.KD.TwoHS.HarSylD.parC
#krows32 CFSG.KD.TwoHS.CLab CFSG.KD.TwoHS.HarSylD.labC
#krows32 CFSG.KD.TwoHS.WPar CFSG.KD.TwoHS.HarSylD.parW
#krows32 CFSG.KD.TwoHS.WLab CFSG.KD.TwoHS.HarSylD.labW
#krows32 CFSG.KD.TwoHS.CPI CFSG.KD.TwoHS.HarSylD.invC
#krows32 CFSG.KD.TwoHS.WPI CFSG.KD.TwoHS.HarSylD.invW

end
