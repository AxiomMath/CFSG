module

public import Certificates.Kernel.RouteP.Bridge.Defs
public import Certificates.Kernel.RouteP.Data.Rel3U
import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.Sporadic.Presentation.Common
public import Mathlib

public section

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP

@[expose] def wU3 : List Int := [31, -30, 29, 38, -39, 31, -32, 33, -34, 37, -31, 35, -36]

@[expose] def qkT3 : List (List Int) :=
  [[36, -37, 36, -37, 0], [37, -38, 37, -38, 0], [37, -39, 37, -39, 0],
    [-42, -42, -42, -42, -42, -42, -42, -42, -42], [-42, -29, 42, 29], [-42, -30, 42, 30],
    [-42, -31, 42, 31], [-42, -32, 42, 32], [-42, -33, 42, 33], [-42, -34, 42, 34], [-42, -35, 42, 35],
    [-42, -36, 42, 36], [-42, -37, 42, 37], [-42, -38, 42, 38], [-42, -39, 42, 39],
    List.replicate 17 43 ++ [42]]

@[expose] def qiT3 : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
    14]

@[expose] noncomputable def qckU3 (g : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (idKOK NWU3 KAU3 KBU3 (List.getD qkT3 (Nat.div g 20) []))
    (idOK NWU3 (List.getD qkT3 (Nat.div g 20) []) (Nat.mod g 20)) (Nat.blt (Nat.mod g 20) 19)

@[expose] noncomputable def uckU3 (k : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (andB (CFSG.KC.Fi24Net.netOK (NWU3 (nat_lit 42))) (kapOK KAU3 KBU3 (nat_lit 42)))
      (wordKOK NWU3 KAU3 KBU3 wU3 (nat_lit 42)) (Nat.blt k 20))
    (wordOK NWU3 wU3 (nat_lit 42) k) (Nat.blt k 19)

end CFSG.KD.RouteP

#kc_slice_range CFSG.KD.RouteP.uckU3 CFSG.KD.RouteP.BridgeCk.u 0 21
#kc_slice_range CFSG.KD.RouteP.qckU3 CFSG.KD.RouteP.BridgeCk.r 0 320

end
