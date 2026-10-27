module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.Misc.HexFlat
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Tables
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Tables
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.Open.Defs

set_option maxRecDepth 400000

#ks_chars CFSG.KD.HN1408.H8 CFSG.EvenSporadicStandard.HNRecog.h1408Hex
#kmisc_hexflat CFSG.KD.HN1408.H8 CFSG.EvenSporadicStandard.HNRecog.h1408Hex 3 1408 11 7

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

theorem h8_ok : allN 7 (fun j => bAnd(canonK 1408 11 (mask 11) (1408 * 11) (H8.F j),
    invEqK 1408 11 (mask 11) (1408 * 11) (H8.F j) (H8.F j))) = true := by
  quickRfl

end CFSG.KD.HN1408

end
