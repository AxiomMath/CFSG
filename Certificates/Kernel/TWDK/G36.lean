module

public import CFSG.Certificates.Kernel.TWDK36Sound
public import Certificates.Kernel.TWDK.C36
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.TWDK36

open Certificates.TWDK Certificates.TWDK36

#kc_forall_tree allS (fun i => kOneAt 3 6 F O S i = true) 14 CFSG.KD.TWDK36.s

#kc_forall_tree allT (fun i => kTwoAt 3 6 F O T i = true) 8 CFSG.KD.TWDK36.t

theorem cells : CFSG.StandardType.GGTWDCells36Orb := by
  refine CFSG.StandardType.TWDK36.twdk36_cells F O S T frame cover
    (fun i hi => allS i ?_) (fun i hi => allT i ?_)
  · rwa [lenS] at hi
  · rwa [lenT] at hi

end CFSG.KD.TWDK36

end
