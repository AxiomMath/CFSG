module

public import CFSG.Certificates.Kernel.TWLKSound
public import Certificates.Kernel.TWLK.C39
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TWLK39

open Certificates.TWLK

#kc_forall_tree allS (fun i => kPat1At 3 9 RF (kRT8 3 9 H E) S i = true) 20 CFSG.KD.TWLK39.l39s

#kc_forall_tree allT (fun i => kPat2At 3 9 RF (kRT8 3 9 H E) T i = true) 8 CFSG.KD.TWLK39.l39t

theorem cells : CFSG.StandardType.GGTWLowCells 3 9 CFSG.StandardType.GGTWLowE8Outcome := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine CFSG.StandardType.TWLK.twlk_sound (by norm_num) (by norm_num)
    (CFSG.StandardType.TWLK.kRT8_sound H E) RF S T roots cover
    (fun i hi => allS i ?_) (fun i hi => allT i ?_)
  · rwa [lenS] at hi
  · rwa [lenT] at hi

end CFSG.KD.TWLK39

end
