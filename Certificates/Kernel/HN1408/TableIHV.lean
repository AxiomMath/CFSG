module

public import Certificates.Kernel.HN1408.TableIData
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.HN1408.TableIData
meta import Certificates.Data.CFSGNative.SmallOddCore.Check

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TIGen

meta def hv1 : Array (Array Nat) :=
  r1.map fun t => #[(CFSG.Sporadic.SmallOddCore.Native.hkey 1408 (t.map UInt32.ofNat)).toNat]

meta def hv3 : Array (Array Nat) :=
  r3.map fun t => #[(CFSG.Sporadic.SmallOddCore.Native.hkey 1408 (t.map UInt32.ofNat)).toNat]

end CFSG.KD.HN1408.TIGen

end

#kmisc_packarrs CFSG.KD.HN1408.TI1V CFSG.KD.HN1408.TIGen.hv1 64
#kmisc_packarrs CFSG.KD.HN1408.TI3V CFSG.KD.HN1408.TIGen.hv3 64
