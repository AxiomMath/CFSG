module

public import Certificates.Kernel.HN1408.M11Data
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.HN1408.M11Data
meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.M11Gen

meta def hvA : Array (Array Nat) :=
  rA.map fun t => #[(CFSG.Sporadic.SmallOddCore.Native.hkey 1408 (t.map UInt32.ofNat)).toNat]

end CFSG.KD.HN1408.M11Gen

end

#kc_items CFSG.KD.HN1408.MR1V include_bytes "data/M11HV.MR1V.items" 95014 13657528082935634750
