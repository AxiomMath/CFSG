module

public import CFSG.Certificates.Kernel.TWLKFSound
public import Certificates.Kernel.TWLKF.C77
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TWLKF77

open Certificates.TWLK Certificates.TWLKF

#kc_forall_tree allS (fun i => kPat1NAt 7 7 RF S i = true) 16 CFSG.KD.TWLKF77.twf77s

#kc_forall_tree allT (fun i => kPat2NAt 7 7 RF T i = true) 8 CFSG.KD.TWLKF77.twf77t

theorem cells : CFSG.StandardType.GGTWCells .frame 7 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine CFSG.StandardType.TWLKF.twlkF_sound (by norm_num) (by norm_num) RF S T roots cover
    (fun i hi => allS i ?_) (fun i hi => allT i ?_)
  · rwa [lenS] at hi
  · rwa [lenT] at hi

end CFSG.KD.TWLKF77

end
