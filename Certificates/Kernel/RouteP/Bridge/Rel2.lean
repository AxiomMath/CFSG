module

public import Certificates.Kernel.RouteP.Bridge.Defs
import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.Sporadic.Presentation.Common
public import Mathlib

public section

namespace CFSG.KD.RouteP

@[expose] def qkT2 : List (List Int) :=
  [[31, -37, 31, -37, 0], [32, -37, 32, -37, 0], [33, -37, 33, -37, 0],
    [34, -37, 34, -37, 34, -37, 0], [35, -37, 35, -37, 0]]

@[expose] def qiT2 : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]

@[expose] noncomputable def qck2 (g : Nat) : Bool := qckT qkT2 g

end CFSG.KD.RouteP

#kc_slice_range CFSG.KD.RouteP.qck2 CFSG.KD.RouteP.BridgeCk.t 0 100

end
