module

public import CFSG.Sporadic.HeldB.CertPBridgeData
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.Kernel.Misc.HexFlat
public meta import CFSG.Sporadic.HeldB.CertPBridgeData
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.Sporadic.OddCore.RowsCmd

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He2111

meta def piM : Array Nat :=
  CFSG.Monster.B.Co2.Native.invCand 8330 CFSG.Sporadic.HeldB.heBridgeArr

end CFSG.KD.He2111

end

set_option maxRecDepth 400000

#ks_chars CFSG.KD.He2111.BrT CFSG.Sporadic.HeldB.heBridgeHex
#kmisc_hexflat CFSG.KD.He2111.BrT CFSG.Sporadic.HeldB.heBridgeHex 4 8330 14 1
#ks_chars CFSG.KD.He2111.GnT CFSG.Sporadic.HeldB.heGenHex
#kmisc_hexflat CFSG.KD.He2111.GnT CFSG.Sporadic.HeldB.heGenHex 4 8330 14 2
#krows CFSG.KD.He2111.PI CFSG.KD.He2111.piM
