module

public import CFSG.Certificates.Kernel.TWDKSound
public import Certificates.Kernel.TWDK.C510S
public import Certificates.Kernel.TWDK.C510R
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TWDK510

open Certificates.TWDK

#kc_forall_tree allS (fun i => kSingleAt 5 10 F S i = true) 20 CFSG.KD.TWDK510.s

#kc_forall_tree allR (fun i => kResAt 5 10 F R i = true) 4 CFSG.KD.TWDK510.r

theorem cells : CFSG.StandardType.GGTWDCells 5 10 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine CFSG.StandardType.TWDK.twdk_cells (by decide) (by decide) (by decide) F S R frame cover
    (fun i hi => allS i ?_) (fun i hi => allR i ?_)
  · rwa [lenS] at hi
  · rwa [lenR] at hi

end CFSG.KD.TWDK510

end
