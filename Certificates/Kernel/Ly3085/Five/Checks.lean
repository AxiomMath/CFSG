
module

public import Certificates.Kernel.LyFiveL1.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LyFive

open CFSG.KC.LyFive CFSG.KC.LyOm CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord CFSG.KD.LyOm
  CFSG.RankThree.Native CFSG.RankThree.PartOne.LyFive

@[expose] noncomputable def trOK (t : List ℤ) (W : Nat) : Bool :=
  letB (fMul BC (fMul BC (wordF BC GAB ((t.reverse.map abL).map fun l => (l + 2) % 4)) W)
      (wordF BC GAB (t.map abL))) (fun Z => Nat.beq (fMul BC Z EL) (fMul BC EL Z))

theorem trX : trOK xWord (UG 20) = true := by quickRfl
theorem trY3 : trOK y3Word (fMul BC (UG 4) (UG 8)) = true := by quickRfl
theorem trY1 : trOK y1Word (fMul BC (UG 4) (UG 8)) = true := by quickRfl

@[expose] def tAW : List Nat := ((List.replicate 4 [2, 2, 3, 3, 3, 1, 2, 2, 1, 1]).flatten).map hL

@[expose] def tBW : List Nat := ((List.replicate 2 [0, 2, 3, 3, 2, 3, 3, 2, 2, 1]).flatten).map hL

theorem gx : letB (wordF BC UG GX) (fun G => Nat.beq (fMul BC G (wordF BC UG tAW))
    (fMul BC (UG 20) G)) = true := by quickRfl

theorem gy : letB (wordF BC UG GY) (fun G => Nat.beq (fMul BC G (wordF BC UG tBW))
    (fMul BC (fMul BC (UG 4) (UG 8)) G)) = true := by quickRfl

end CFSG.KD.LyFive

end
