module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Sporadic.SmallOddCore.HSData
meta import CFSG.Sporadic.SmallOddCore.HSData
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HSIrr.D

open CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

meta def idM : Array Nat := idTab 3850

meta def gS : Array (Array Nat) := (hsSylowGenTbls.map natArr).toArray

meta def idsS : Array (Array Nat) := Array.replicate gS.size idM

meta def giS : Array (Array Nat) := gS.map (CFSG.Monster.B.Co2.Native.invCand 3850)

meta def recS : Array (Array Nat) := (bfs (fun j t => conjTab 3850 idM gS[j]! t) gS.size idM 1100).tabs

meta def clS : Array (Array Nat) := (recS.map fun x => (gS ++ giS).map fun g => comp 3850 x g).flatten

end CFSG.KD.HSIrr.D

#kmulh CFSG.KD.HSIrr.SR 3850 12 CFSG.KD.HSIrr.D.idsS CFSG.KD.HSIrr.D.gS CFSG.KD.HSIrr.D.idM 1100
#kmisc_packarrs CFSG.KD.HSIrr.SRI CFSG.KD.HSIrr.D.giS 12
#kfind CFSG.KD.HSIrr.SRCl CFSG.KD.HSIrr.D.recS CFSG.KD.HSIrr.D.clS

end
