module

public import Certificates.Data.Kernel.U43.Class
public import Certificates.Kernel.U43C.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.U43C

open CFSG.KC.Loop CFSG.KD.G2Three CFSG.KD.U43 CFSG.RankThree.PartTwo.Sec4.Item434RemU43

theorem c9575Data_ok : (uLiftBasis.length == 4 && uLiftBasis.all (· < 729) && uRt.length == 81 &&
    uRt.all (· < 729) && uKind.length == 729 && decide (uB0 < 729) && decide (uZ < 729) &&
    uConvR.all fun e => wordOK e.2) = true := by quickRfl

theorem c9575Letters_ok : lettersF UAF = true := by quickRfl

theorem c9575Gens_ok :
    allBelow 3 1 (fun s => Nat.beq (UGF s) (wordF UAF (uGenWords.getD s []))) = true := by
  quickRfl

theorem c9575One_ok : Nat.beq (UXF 0) ONEF = true := by quickRfl

theorem c9575Par_ok : parF UXF UGF 3 uPar 0 = true := by quickRfl

theorem c9575Rt_ok : rtK UXF RTP RTI = true := by quickRfl

theorem c9575Kind_ok : kindF UXF UAF (UXF uB0) uKind 0 = true := by quickRfl

theorem c9575Z_ok : zF UXF (UXF uZ) = true := by quickRfl

theorem c9575Cent_ok : centF UXF (UXF uB0) = true := by quickRfl

theorem c9575OGens_ok : (Nat.beq (OX 0) (UXF uB0) &&
    allBelow 2 1 (fun s => Nat.beq (OGA s) (wordF UAF [s]) &&
      Nat.beq (OGB s) (wordF UAF (invWord [s])))) = true := by quickRfl

theorem c9575OPar0_ok : oparF OX OGA OGB 40319 ((uOrbParW.drop 0).take 79) 0 = true := by
  quickRfl
theorem c9575OPar1_ok : oparF OX OGA OGB 40319 ((uOrbParW.drop 79).take 79) 79 = true := by
  quickRfl
theorem c9575OPar2_ok : oparF OX OGA OGB 40319 ((uOrbParW.drop 158).take 79) 158 = true := by
  quickRfl
theorem c9575OPar3_ok : oparF OX OGA OGB 40319 ((uOrbParW.drop 237).take 79) 237 = true := by
  quickRfl
theorem c9575OPar4_ok : oparF OX OGA OGB 40319 ((uOrbParW.drop 316).take 79) 316 = true := by
  quickRfl
theorem c9575OPar5_ok : oparF OX OGA OGB 40319 ((uOrbParW.drop 395).take 79) 395 = true := by
  quickRfl
theorem c9575OPar6_ok : oparF OX OGA OGB 40319 ((uOrbParW.drop 474).take 79) 474 = true := by
  quickRfl
theorem c9575OPar7_ok : oparF OX OGA OGB 40319 ((uOrbParW.drop 553).take 79) 553 = true := by
  quickRfl

theorem c9575OSort_ok : sortK OX OSRT OSRI 40320 630 = true := by quickRfl

end CFSG.KD.U43C

end
