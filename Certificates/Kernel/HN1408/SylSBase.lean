module

public import Certificates.Kernel.HN1408.SylS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.BaseMask
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel

theorem sylS_cnt : SylS.cnt = 2048 := rfl

theorem sylS_k : SylS.k = 5 := rfl

theorem sylS_hd : penumHdK idK SylS.cnt 4096 SylS.T SylS.PL = true := by quickRfl

theorem sylS_gens : allN 5 (fun j => Nat.beq (SylS.G j) (WK (sWords.getD j []))) = true := by
  quickRfl

theorem sylS_bsort : allN 2048 (bsortPtK 1408 11 (mask 11) 2 0 2048 SylS.T SylS.KS SylS.KSI) =
    true := by
  quickRfl

theorem sylS_inv : involMaskK 11 (mask 11) 2 0 2048 SylS.T SylS.IV nIV = true := by quickRfl

theorem sylS_inv_neg : (!involMaskK 11 (mask 11) 2 0 2048 SylS.T SylS.IV 302) = true := by
  quickRfl

theorem sylS_cm : strictB ivMask (fun M => allN nGD (fun j =>
    cmaskK 11 (mask 11) 2 0 SylS.T SylS.IV nIV M (SylS.CM j) (r32 SylS.GD j))) = true := by
  quickRfl

end CFSG.KD.HN1408

end
