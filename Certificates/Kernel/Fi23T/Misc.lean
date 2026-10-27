module

public import Certificates.Data.Kernel.Fi23T.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23T.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KD.Fi23K

theorem fc_moved : Bool.not (Nat.beq (tb G (nat_lit 43) (nat_lit 11504)) (nat_lit 11504)) = true := by
  quickRfl

theorem cs_pts : bAnd(domR H (nat_lit 71), domR H (nat_lit 92)) = true := by quickRfl

theorem neg_fc_moved : Bool.not (Bool.not (Nat.beq (tb G (nat_lit 43) (tb H (nat_lit 0) (nat_lit 0)))
    (tb H (nat_lit 0) (nat_lit 0)))) = true := by quickRfl

theorem neg_cs_pts : Bool.not (domR H (nat_lit 37)) = true := by quickRfl

end CFSG.KD.Fi23T

end
