module

public import Certificates.Kernel.HN1408.SylS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.AData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.BaseMask CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel

theorem sylS_az : bAnd(Nat.beq (SylS.T (r32 SylS.FM 1)) (WK wordA),
    Nat.beq (SylS.T (r32 SylS.FM 2)) (WK wordZ)) = true := by
  quickRfl

theorem sylS_A : bAnd(memberK 11 (mask 11) 2 0 2048 SylS.T SylS.FA 0 6,
    bAnd(allN 6 (fun j => Nat.beq (SylS.T (r32 SylS.FA (Nat.shiftLeft 1 j))) (WK (uWords.getD j []))),
      Nat.beq (maskK SylS.FA 0 64) (maskK SylS.FM 6188 64))) = true := by
  quickRfl

theorem sylS_y : Nat.beq (SylS.T (r32 SylS.Y 0)) (SylS.G 4) = true := by quickRfl

theorem sylS_conj : bAnd(conjMemK 11 (mask 11) 2 0 SylS.T SylS.FA SylS.FC (r32 SylS.Y 0) 64,
    Nat.beq (maskK SylS.FC 0 64) (maskK SylS.FM 6252 64)) = true := by
  quickRfl

theorem sylS_conj_neg : (!conjMemK 11 (mask 11) 2 0 SylS.T SylS.FA SylS.FC 0 64) = true := by
  quickRfl

end CFSG.KD.HN1408

end
