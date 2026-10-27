module

import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.StrChunks
public import Certificates.Data.Kernel.Spor.BytesF
public import Certificates.Data.CFSGNative.Fi24.Data
public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import CFSG.Certificates.Kernel.Common.StrChunks

public section

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

#str_chunks CFSG.KD.BrFi24.SA CFSG.Sporadic.Fi24.Native.seedA 1048576 10000000 2048

#str_chunks CFSG.KD.BrFi24.SB CFSG.Sporadic.Fi24.Native.seedB 1048576 10000000 2048

namespace CFSG.KD.BrFi24

theorem seed1_run : CFSG.KS.Bytes.runF P1 256 617792 SA.chars 0 = true := by quickRfl

theorem seed2_run : CFSG.KS.Bytes.runF P2 256 617792 SB.chars 0 = true := by quickRfl

end CFSG.KD.BrFi24

end
