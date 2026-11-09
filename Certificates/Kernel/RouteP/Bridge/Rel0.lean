module

public import Certificates.Kernel.RouteP.Bridge.Defs
import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.Sporadic.Presentation.Common
public import Mathlib

public section

namespace CFSG.KD.RouteP

@[expose] def qkT0 : List (List Int) :=
  [[-29, -29, -29], [-30, -30], [-31, -31], [-32, -32], [-33, -33], [-34, -34], [-35, -35],
    [-36, -36], [-38, -38, -38], [-39, -39], [29, -30, 29, -30, 29, -30], [29, -31, 29, -31],
    [29, -32, 29, -32], [29, -33, 29, -33], [29, -34, 29, -34], [29, -35, 29, -35],
    [29, -36, 29, -36], [29, -38, 29, -38], [29, -39, 29, -39], [30, -31, 30, -31, 30, -31],
    [30, -32, 30, -32], [30, -33, 30, -33], [30, -34, 30, -34], [30, -35, 30, -35],
    [30, -36, 30, -36], [30, -38, 30, -38], [30, -39, 30, -39], [31, -32, 31, -32, 31, -32],
    [31, -33, 31, -33], [31, -34, 31, -34], [31, -35, 31, -35, 31, -35], [31, -36, 31, -36]]

@[expose] def qiT0 : List Nat :=
  [0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14,
    14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22, 23, 23, 24, 24, 25, 25, 26,
    26, 27, 27, 28, 28, 29, 29, 30, 30, 31, 31]

@[expose] noncomputable def qck0 (g : Nat) : Bool := qckT qkT0 g

end CFSG.KD.RouteP

#kc_slice_range CFSG.KD.RouteP.qck0 CFSG.KD.RouteP.BridgeCk.q 0 640

end
