module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T

theorem root_8_0 : Nat.beq (tb H (nat_lit 8) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem root_28_0 : Nat.beq (tb H (nat_lit 28) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem root_36_0 : Nat.beq (tb H (nat_lit 36) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem root_32_0 : Nat.beq (tb H (nat_lit 32) (nat_lit 0)) (nat_lit 71) = true := by quickRfl

theorem root_12_0 : Nat.beq (tb H (nat_lit 12) (nat_lit 0)) (nat_lit 2) = true := by quickRfl

theorem root_16_0 : Nat.beq (tb H (nat_lit 16) (nat_lit 0)) (nat_lit 2) = true := by quickRfl

theorem root_16_1 : Nat.beq (tb H (nat_lit 16) (nat_lit 1)) (nat_lit 5) = true := by quickRfl

theorem root_16_22401 : Nat.beq (tb H (nat_lit 16) (nat_lit 22401)) (nat_lit 3) = true := by
  quickRfl

theorem root_16_25551 : Nat.beq (tb H (nat_lit 16) (nat_lit 25551)) (nat_lit 8) = true := by
  quickRfl

theorem root_20_0 : Nat.beq (tb H (nat_lit 20) (nat_lit 0)) (nat_lit 2) = true := by quickRfl

theorem root_20_2916 : Nat.beq (tb H (nat_lit 20) (nat_lit 2916)) (nat_lit 3) = true := by
  quickRfl

theorem root_20_22599 : Nat.beq (tb H (nat_lit 20) (nat_lit 22599)) (nat_lit 8) = true := by
  quickRfl

theorem root_20_25515 : Nat.beq (tb H (nat_lit 20) (nat_lit 25515)) (nat_lit 17) = true := by
  quickRfl

theorem root_24_0 : Nat.beq (tb H (nat_lit 24) (nat_lit 0)) (nat_lit 0) = true := by quickRfl

theorem root_24_2916 : Nat.beq (tb H (nat_lit 24) (nat_lit 2916)) (nat_lit 2) = true := by
  quickRfl

theorem root_24_5832 : Nat.beq (tb H (nat_lit 24) (nat_lit 5832)) (nat_lit 3) = true := by
  quickRfl

theorem root_24_25515 : Nat.beq (tb H (nat_lit 24) (nat_lit 25515)) (nat_lit 8) = true := by
  quickRfl

theorem xi_in : allN (nat_lit 10) (fun i => domT H (tb H (nat_lit 40) i)) = true := by quickRfl

theorem cg_in : allN (nat_lit 9) (fun i => domO H (tb H (nat_lit 41) i)) = true := by quickRfl

theorem neg_xi_in : Bool.not (allN (nat_lit 10) (fun i => domO H (tb H (nat_lit 40) i))) = true := by
  quickRfl

theorem neg_roots : Bool.not (Nat.beq (tb H (nat_lit 16) (nat_lit 1)) (nat_lit 3)) = true := by
  quickRfl

end CFSG.KD.Fi23T

end
