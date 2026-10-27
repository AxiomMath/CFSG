module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.Misc.HexFlat
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

set_option maxRecDepth 400000

#ks_chars CFSG.KD.TwoHS.HY CFSG.EvenSporadicStandard.TwoHS.harHex
#kmisc_hexflat CFSG.KD.TwoHS.HY CFSG.EvenSporadicStandard.TwoHS.harHex 4 11200 14 6

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

theorem hy_ok : allN 6 (fun j => bAnd(canonK 11200 14 (mask 14) (11200 * 14) (HY.F j),
    invEqK 11200 14 (mask 14) (11200 * 14) (HY.F j) (HY.F j))) = true := by
  quickRfl

end CFSG.KD.TwoHS

end
