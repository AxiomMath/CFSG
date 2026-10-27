module

public import CFSG.Quasithin.H13.KGFactT3J4Inputs
public import Certificates.Kernel.M24Dc.Idx3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.M24Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H13.KGT3J4
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open CFSG.Sporadic.J4.QT

theorem t3j4_inv :
    ∀ k < 3, ∀ q < 24, (invTab24 (starPermOf k)).getD ((starPermOf k).getD q 0) 0 = q := by
  decide +kernel

theorem t3j4_fixLab :
    ∀ i < 4, codeSetAct 24 (starWordTab (kWords.getD i [])).toArray t3yLab = t3yLab := by
  unfold t3yLab t3yTab
  rw [wordTabA_eq_L, codeSetAct_eq, delta_eqK]
  decide +kernel

theorem t3j4_norm :
    ∀ i < 4, ∀ v ∈ [422, 553, 1131], actT (kTab i) v ∈ CFSG.Quasithin.J4Loc.V0L := by
  decide +kernel

theorem t3j4_cent : ∀ v ∈ [422, 553, 1131], actT (wordT t3cWord) v = v := by
  decide +kernel

theorem t3j4Check : T3J4Check := ⟨t3j4_inv, t3j4_fixLab, t3j4_norm, t3j4_cent⟩

end CFSG.KD.M24Dc

end
