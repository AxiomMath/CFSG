
module

public import Certificates.Kernel.MonsterB.Fischer3065T
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelMonB.F3065

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Sporadic.SmallF2.Native
  CFSG.KC.FischerK CFSG.KC.FischerE CFSG.KLie.CT

theorem kInvG : gramInvCheck = true := by decide +kernel

theorem kGT : (transposeRows 78 gramRowArr).toList = FD.GT := by decide +kernel

theorem kNcLen : GramLit.ncRows.length = 78 := by decide +kernel

theorem kCoord1 : ((List.range 78).all fun i => labelCoord (basisPt i) == 2 ^ i) = true := by
  decide +kernel

theorem kCoord2 :
    allIdx (fun y c => vecMulL FD.GT c == colN GramLit.ncRows y) GramLit.rowCoords 0 = true := by
  decide +kernel

theorem kBasis : (List.range 78).map basisPt =
    [0, 1, 2, 3, 4, 6, 7, 8, 10, 12, 14, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 38,
      39, 40, 42, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 66, 70, 71, 72, 74, 86, 87, 88, 90,
      94, 102, 118, 150, 151, 152, 154, 158, 166, 182, 278, 279, 282, 286, 294, 310, 406, 534,
      535, 538, 566, 1046, 1047, 1078, 1110, 1174, 1270, 1334, 1462, 1686, 1942, 2326] := by
  decide +kernel

end CertificateChecks.KernelMonB.F3065

end
