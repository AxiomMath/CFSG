module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KC.Fi23C CFSG.KD.Fi23K

theorem x0_cnt : cntK G H [nat_lit 2] (nat_lit 360) = true := by quickRfl

theorem dom_ok : bAnd(domTc H (nat_lit 2), bAnd(domTc H (nat_lit 5),
    bAnd(domO H (nat_lit 37), bAnd(Nat.beq (cJ G (nat_lit 37) (nat_lit 2)) (nat_lit 2),
      bAnd(domO H (nat_lit 0), Bool.not (Nat.beq (cJ G (nat_lit 0) (nat_lit 2)) (nat_lit 2))))))) =
    true := by quickRfl

theorem k_gens : genK G H (nat_lit 42) (nat_lit 5) true (nat_lit 2) [] = true := by quickRfl
theorem kv_gens : genK G H (nat_lit 43) (nat_lit 5) false (nat_lit 0) [nat_lit 5, nat_lit 2] =
    true := by quickRfl

theorem cr_5 : cntK G H [nat_lit 2, nat_lit 5] (nat_lit 324) = true := by quickRfl
theorem cr_3 : bAnd(qK G H [nat_lit 3, nat_lit 2, nat_lit 6617], domTc H (nat_lit 6617)) = true := by
  quickRfl
theorem cr_8 : bAnd(qK G H [nat_lit 8, nat_lit 2, nat_lit 8], domTc H (nat_lit 8)) = true := by
  quickRfl

theorem dr_2 : bAnd(qK G H [nat_lit 5, nat_lit 2, nat_lit 2, nat_lit 5], domTc H (nat_lit 5)) =
    true := by quickRfl
theorem dr_3 : cntK G H [nat_lit 3, nat_lit 2, nat_lit 5] (nat_lit 324) = true := by quickRfl
theorem dr_8 : bAnd(qK G H [nat_lit 9702, nat_lit 8, nat_lit 2, nat_lit 5], domTc H (nat_lit 9702)) =
    true := by quickRfl
theorem dr_17 : cntK G H [nat_lit 17, nat_lit 2, nat_lit 5] (nat_lit 324) = true := by quickRfl

theorem er_0 : bAnd(qK G H [nat_lit 5, nat_lit 2, nat_lit 0, nat_lit 2176, nat_lit 8],
    domW G H [nat_lit 8] (nat_lit 2176)) = true := by quickRfl
theorem er_3: bAnd(qK G H [nat_lit 5, nat_lit 2, nat_lit 3, nat_lit 4776, nat_lit 5],
    domW G H [nat_lit 5] (nat_lit 4776)) = true := by quickRfl
theorem er_3m : bAnd(qK G H [nat_lit 3346, nat_lit 5, nat_lit 2, nat_lit 5],
    domTc H (nat_lit 3346)) = true := by quickRfl

theorem mu_gens : allN (nat_lit 5) (fun i => domW G H [nat_lit 2] (tb H (nat_lit 43) i)) = true := by
  quickRfl
theorem mu_cross : bAnd(qK G H [nat_lit 2, nat_lit 27573, nat_lit 8],
    domW G H [nat_lit 2] (nat_lit 27573)) = true := by quickRfl

theorem ga_ok : bAnd(qK G H [nat_lit 4600, nat_lit 31710], domTc H (nat_lit 4600)) = true := by
  quickRfl
theorem gb_ok : bAnd(qK G H [nat_lit 1558, nat_lit 7, nat_lit 31711],
    bAnd(domTc H (nat_lit 7), domTc H (nat_lit 1558))) = true := by quickRfl

end CFSG.KD.Fi23T

end
