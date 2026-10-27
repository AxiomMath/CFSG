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

theorem c9575OGens_ok : (Nat.beq (OX 0) (UXF uB0) && Nat.beq (wC (OW 0)) 1 &&
    Nat.beq (wC (OW 40320)) 40320 &&
    allBelow 2 1 (fun s => Nat.beq (OGA s) (wordF UAF [s]) &&
      Nat.beq (OGB s) (wordF UAF (invWord [s])))) = true := by quickRfl

theorem c9575Orb0_ok : ostepF OX OGA OGB OW OPP 40320 0 5040 79 = true := by quickRfl
theorem c9575Orb1_ok : ostepF OX OGA OGB OW OPP 40320 5040 5040 79 = true := by quickRfl
theorem c9575Orb2_ok : ostepF OX OGA OGB OW OPP 40320 10080 5040 79 = true := by quickRfl
theorem c9575Orb3_ok : ostepF OX OGA OGB OW OPP 40320 15120 5040 79 = true := by quickRfl
theorem c9575Orb4_ok : ostepF OX OGA OGB OW OPP 40320 20160 5040 79 = true := by quickRfl
theorem c9575Orb5_ok : ostepF OX OGA OGB OW OPP 40320 25200 5040 79 = true := by quickRfl
theorem c9575Orb6_ok : ostepF OX OGA OGB OW OPP 40320 30240 5040 79 = true := by quickRfl
theorem c9575Orb7_ok : ostepF OX OGA OGB OW OPP 40320 35280 5040 79 = true := by quickRfl

theorem c9575OSort_ok : sortK OX OSRT OSRI 40320 630 = true := by quickRfl

end CFSG.KD.U43C

end
