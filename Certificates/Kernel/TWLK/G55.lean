module

public import CFSG.Certificates.Kernel.TWLKSound
public import Certificates.Kernel.TWLK.C55
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TWLK55

open Certificates.TWLK

#kc_forall_tree allS (fun i => kPat1At 5 5 RF (kRTPZ 5 5 H Z) S i = true) 12 CFSG.KD.TWLK55.l55s

#kc_forall_tree allT (fun i => kPat2At 5 5 RF (kRTPZ 5 5 H Z) T i = true) 8 CFSG.KD.TWLK55.l55t

theorem cells : CFSG.StandardType.GGTWLowCells 5 5 (fun _ => False) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine CFSG.StandardType.TWLK.twlk_sound (by norm_num) (by norm_num)
    (CFSG.StandardType.TWLK.kRTPZ_sound (by norm_num) (by norm_num) _ H Z) RF S T roots cover
    (fun i hi => allS i ?_) (fun i hi => allT i ?_)
  · rwa [lenS] at hi
  · rwa [lenT] at hi

end CFSG.KD.TWLK55

end
