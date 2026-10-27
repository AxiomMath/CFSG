module

public import Certificates.Kernel.HS589207.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589207.Gen

open CFSG.KC.DcHSOutK CFSG.KC.Enum CFSG.Quasithin.H13.LocDbl.HSLoc

theorem gens : (allN 4 (fun l => ltF (A l)) && ltF uF &&
    eqF (fun q => A 0 (A 2 q)) (fun q => q) && eqF (fun q => A 2 (A 0 q)) (fun q => q) &&
    eqF (fun q => A 1 (A 3 q)) (fun q => q) && eqF (fun q => A 3 (A 1 q)) (fun q => q)) = true := by
  quickRfl

theorem mgens : (eqF (GM 0) (CFSG.KC.E64F.wordF A (mWords.getD 0 [])) &&
    eqF (GM 1) (CFSG.KC.E64F.wordF A (mWords.getD 1 []))) = true := by
  quickRfl

theorem wtab : (eqF gF (ePath FP FL A 3850 kU) && eqF wF (fun q => uF (gF q)) &&
    eqF r0F (fun q => wF (mF i0 q)) && ltF gF && ltF wF && ltF r0F) = true := by
  quickRfl

theorem moore : mooreK = true := by quickRfl

theorem goodInv : allN 10 (fun j => ltF (invG j) &&
    eqF (fun q => mF (goodIdx.getD j 0) (invG j q)) (fun q => q) &&
    eqF (fun q => invG j (mF (goodIdx.getD j 0) q)) (fun q => q)) = true := by
  quickRfl

theorem goodDist : allN 10 (fun a => allN 10 (fun b => !Nat.blt a b || !eqF (cF a) (cF b))) =
    true := by
  quickRfl

theorem goodOut : allN 10 (fun j => IO.contains (IG.getD j 0) &&
    eqF (fun q => wF (mF (IG.getD j 0) q)) (cF j)) = true := by
  quickRfl

end CFSG.KD.HS589207.Gen

end
