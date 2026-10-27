module

public import CFSG.Certificates.Kernel.TWLKFSound
public import Certificates.Kernel.TWLKF.C510
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TWLKF510

open Certificates.TWLK Certificates.TWLKF

#kc_forall_tree allS (fun i => kPat1NAt 5 10 RF S i = true) 20 CFSG.KD.TWLKF510.twf510s

#kc_forall_tree allT (fun i => kPat2NAt 5 10 RF T i = true) 8 CFSG.KD.TWLKF510.twf510t

theorem cells : CFSG.StandardType.GGTWCells .frame 5 10 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine CFSG.StandardType.TWLKF.twlkF_sound (by norm_num) (by norm_num) RF S T roots cover
    (fun i hi => allS i ?_) (fun i hi => allT i ?_)
  · rwa [lenS] at hi
  · rwa [lenT] at hi

end CFSG.KD.TWLKF510

end
