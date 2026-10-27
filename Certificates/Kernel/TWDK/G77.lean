module

public import CFSG.Certificates.Kernel.TWDKSound
public import Certificates.Kernel.TWDK.C77S0
public import Certificates.Kernel.TWDK.C77S1
public import Certificates.Kernel.TWDK.C77R0
public import Certificates.Kernel.TWDK.C77R1
public import Certificates.Kernel.TWDK.C77R2
public import Certificates.Kernel.TWDK.C77R3
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TWDK77

open Certificates.TWDK

#kc_forall_tree allS (fun i => kSingleAt 7 7 F S i = true) 16 CFSG.KD.TWDK77.s

#kc_forall_tree allR (fun i => kResAt 7 7 F R i = true) 4 CFSG.KD.TWDK77.r

theorem cells : CFSG.StandardType.GGTWDCells 7 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine CFSG.StandardType.TWDK.twdk_cells (by decide) (by decide) (by decide) F S R frame cover
    (fun i hi => allS i ?_) (fun i hi => allR i ?_)
  · rwa [lenS] at hi
  · rwa [lenR] at hi

end CFSG.KD.TWDK77

end
