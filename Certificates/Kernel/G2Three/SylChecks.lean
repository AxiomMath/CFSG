module

public import Certificates.Data.Kernel.G2Three.Syl
public import Certificates.Kernel.G2Three.SylRec
public import Certificates.Kernel.G2Three.Rec
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Check
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

public section

namespace CFSG.KD.G2Three

open CFSG.KC.Ord CFSG.KC.Loop CFSG.RankThree.PartTwo.Sec4.Item434RemG23

theorem sylPar_ok : decide (sylPar = parL (pA (SylPP 0)) (pB (SylPP 0)) 728) = true := by quickRfl

theorem sylBuild_ok : buildK SylX SylG (pA (SylPP 0)) (pB (SylPP 0)) 729 3 12 = true := by quickRfl
theorem sylClose_ok : closeK SylX SylG (fR (SylRTP 0)) 729 3 35 = true := by quickRfl
theorem sylSort_ok : sortK SylX SylSRT SylSRI 729 12 = true := by quickRfl

theorem sylZ_ok : (allL (fun i => Nat.blt i 729 && allBelow 3 1 fun s => commK2 (SylX i) (SylG s))
    sylZ && Nat.blt sylZIdx 729 && allBelow 3 1 (fun s => commK2 (SylX sylZIdx) (SylG s)) &&
    cubeK2 (SylX sylZIdx) && !(Nat.beq (SylX sylZIdx) ONE)) = true := by quickRfl

theorem sylD_ok : allBelow 7 1 (fun j => dBlockK SylX SylDX SylDSRT SylDSRI SylZW (sylDs.getD j [])
    sylZIdx j) = true := by quickRfl

theorem sylW_ok : witK SylX SylDX SylW 729 567 12 = true := by quickRfl

theorem sylT_ok : allBelow 200 4 (fun j => Nat.beq (SylTD j)
    (MUL (MUL (wordK GA (invWord (conjWords.getD (Nat.div j 8) []))) (SylX (sylZ.getD (Nat.mod j 8) 0)))
      (wordK GA (invWord (invWord (conjWords.getD (Nat.div j 8) [])))))) = true := by quickRfl

theorem sylTB_ok : allBelow 729 12 (fun t => !(bitK (SylTB 0) t) ||
    inTK SylTKY SylTD (SylMK 0) (SylX t)) = true := by quickRfl

theorem sylN_ok : decide ((List.range 729).filter (isNK SylX (inTK SylTKY SylTD (SylMK 0))) =
    SylR.map fun R => fR R 0) = true := by quickRfl

theorem sylRC_ok : decide (SylR = SylR0 ++ SylR1 ++ SylR2 ++ SylR3 ++ SylR4 ++ SylR5 ++ SylR6 ++
    SylR7) = true := by quickRfl

theorem sylRow0_ok : allL (rowK (SylPP 0) (SylRTP 0)) SylR0 = true := by quickRfl
theorem sylRow1_ok : allL (rowK (SylPP 0) (SylRTP 0)) SylR1 = true := by quickRfl
theorem sylRow2_ok : allL (rowK (SylPP 0) (SylRTP 0)) SylR2 = true := by quickRfl
theorem sylRow3_ok : allL (rowK (SylPP 0) (SylRTP 0)) SylR3 = true := by quickRfl
theorem sylRow4_ok : allL (rowK (SylPP 0) (SylRTP 0)) SylR4 = true := by quickRfl
theorem sylRow5_ok : allL (rowK (SylPP 0) (SylRTP 0)) SylR5 = true := by quickRfl
theorem sylRow6_ok : allL (rowK (SylPP 0) (SylRTP 0)) SylR6 = true := by quickRfl
theorem sylRow7_ok : allL (rowK (SylPP 0) (SylRTP 0)) SylR7 = true := by quickRfl

theorem sylP0_ok : pairK SylR0 SylR (SylTB 0) = true := by quickRfl
theorem sylP1_ok : pairK SylR1 SylR (SylTB 0) = true := by quickRfl
theorem sylP2_ok : pairK SylR2 SylR (SylTB 0) = true := by quickRfl
theorem sylP3_ok : pairK SylR3 SylR (SylTB 0) = true := by quickRfl
theorem sylP4_ok : pairK SylR4 SylR (SylTB 0) = true := by quickRfl
theorem sylP5_ok : pairK SylR5 SylR (SylTB 0) = true := by quickRfl
theorem sylP6_ok : pairK SylR6 SylR (SylTB 0) = true := by quickRfl
theorem sylP7_ok : pairK SylR7 SylR (SylTB 0) = true := by quickRfl

theorem sylLift_ok : (fun E : Nat → Nat =>
    allBelow 3 1 (fun a => allBelow 3 1 fun b => commK2 (E a) (E b)) &&
    allBelow 3 1 (fun a => cubeK2 (E a)) &&
    allBelow 27 1 (fun u => allBelow 27 1 fun v => Nat.beq u v || !(Nat.beq (lPK E u) (lPK E v))) &&
    allBelow 2 1 (fun j => allBelow 3 1 fun i =>
      Nat.beq (MUL (MUL (wordK GA (liftG.getD j [])) (E i)) (wordK GA (invWord (liftG.getD j []))))
        (MUL (pwK (E 0) (liftMat j 0 i)) (MUL (pwK (E 1) (liftMat j 1 i))
          (MUL (pwK (E 2) (liftMat j 2 i)) ONE)))))
    (fun a => SylX (liftW.getD a 0)) = true := by quickRfl

end CFSG.KD.G2Three

end
