module

public import CFSG.Certificates.Kernel.TWDKSound
public import Certificates.Kernel.TWDK.C39
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TWDK39

open Certificates.TWDK

#kc_forall_tree allS (fun i => kSingleAt 3 9 F S i = true) 20 CFSG.KD.TWDK39.s

#kc_forall_tree allR (fun i => kResAt 3 9 F R i = true) 4 CFSG.KD.TWDK39.r

theorem cells : CFSG.StandardType.GGTWDCells 3 9 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine CFSG.StandardType.TWDK.twdk_cells (by decide) (by decide) (by decide) F S R frame cover
    (fun i hi => allS i ?_) (fun i hi => allR i ?_)
  · rwa [lenS] at hi
  · rwa [lenR] at hi

end CFSG.KD.TWDK39

end
