module

public import CFSG.Certificates.Kernel.TWLKSound
public import Certificates.Kernel.TWLK.C36
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TWLK36

open Certificates.TWLK

#kc_forall_tree allS (fun i => kPat1At 3 6 RF (kRT6 3 6 H Z F) S i = true) 14 CFSG.KD.TWLK36.l36s

#kc_forall_tree allT (fun i => kPat2At 3 6 RF (kRT6 3 6 H Z F) T i = true) 8 CFSG.KD.TWLK36.l36t

theorem cells : CFSG.StandardType.GGTWLowCells 3 6 CFSG.StandardType.GGTWLowE6Outcome := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine CFSG.StandardType.TWLK.twlk_sound (by norm_num) (by norm_num)
    (CFSG.StandardType.TWLK.kRT6_sound frame H Z F) RF S T roots cover
    (fun i hi => allS i ?_) (fun i hi => allT i ?_)
  · rwa [lenS] at hi
  · rwa [lenT] at hi

end CFSG.KD.TWLK36

end
