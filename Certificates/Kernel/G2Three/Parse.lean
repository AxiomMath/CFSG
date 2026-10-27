module

public import Certificates.Kernel.G2Three.Rec
public import Certificates.Data.Kernel.G2Three.Defs
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

set_option maxRecDepth 400000

#ks_chars CFSG.KD.G2Three.PO CFSG.RankThree.PartTwo.Census.Carrier.G2Three.parOStr

public section

namespace CFSG.KD.G2Three

theorem parse_ok : (PO.chars == [';'].intercalate ((List.range 7370).map fun i =>
    pieceChars (OA i) (OB i))) = true := by
  quickRfl

end CFSG.KD.G2Three

end
