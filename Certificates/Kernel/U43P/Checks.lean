module

public import Certificates.Data.Kernel.U43.Pair
public import Certificates.Kernel.U43C.Rec
public import Certificates.Kernel.U43P.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.U43P

open CFSG.KC.Loop CFSG.KD.U43 CFSG.KD.U43C CFSG.RankThree.PartTwo.Sec4.Item434RemU43

theorem c9577Data_ok : (uY.length == 13 && (List.range 13).all (fun n =>
    (yTriple n).length == 3 && (yTriple n).all (· < 729) && wordOK (yWord n)) &&
    uLiftBasis.length == 4 && uLiftBasis.all (· < 729) && uLiftG.length == 2 &&
    uLiftM.length == 2 && uLiftG.all wordOK &&
    (List.range 2).all (fun j => (List.range 4).all fun k => (List.range 4).all fun i =>
      decide (liftMat j k i < 3))) = true := by quickRfl

theorem c9576Sq_ok : sqF UXF SQP = true := by quickRfl

theorem c9576Ol_ok : olF UXF SQP OL OLI = true := by quickRfl

theorem c9576Knd_ok : listF KND uKind 0 = true := by quickRfl

theorem c9576Conv_ok : convF UAF CAP CBP = true := by quickRfl

theorem c9576Pairs0_ok : pairsF UXF SQP KND CAP CBP OL WP WC (UXF uZ) (SQP uZ) 0 37 = true := by
  quickRfl
theorem c9576Pairs1_ok : pairsF UXF SQP KND CAP CBP OL WP WC (UXF uZ) (SQP uZ) 37 37 = true := by
  quickRfl
theorem c9576Pairs2_ok : pairsF UXF SQP KND CAP CBP OL WP WC (UXF uZ) (SQP uZ) 74 37 = true := by
  quickRfl
theorem c9576Pairs3_ok : pairsF UXF SQP KND CAP CBP OL WP WC (UXF uZ) (SQP uZ) 111 37 = true := by
  quickRfl
theorem c9576Pairs4_ok : pairsF UXF SQP KND CAP CBP OL WP WC (UXF uZ) (SQP uZ) 148 37 = true := by
  quickRfl
theorem c9576Pairs5_ok : pairsF UXF SQP KND CAP CBP OL WP WC (UXF uZ) (SQP uZ) 185 37 = true := by
  quickRfl
theorem c9576Pairs6_ok : pairsF UXF SQP KND CAP CBP OL WP WC (UXF uZ) (SQP uZ) 222 37 = true := by
  quickRfl
theorem c9576Pairs7_ok : pairsF UXF SQP KND CAP CBP OL WP WC (UXF uZ) (SQP uZ) 259 37 = true := by
  quickRfl

theorem c9577Y_ok : allBelow 13 1 (yF UXF SQP UAF YR) = true := by quickRfl

theorem c9577Lift_ok : liftK UXF UAF = true := by quickRfl

end CFSG.KD.U43P

end
