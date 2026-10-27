module

public import CFSG.Certificates.Kernel.Orders.Cert3
public import Certificates.Kernel.Sporadic.Fi24Ext.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24Ext

theorem d1 : Nat.beq (CFSG.KC.Ord.decRun3 CFSG.KD.BrFi23.P1 (nat_lit 256) (nat_lit 65042) (nat_lit 253)
    (nat_lit 64009) RM3 (M3 (nat_lit 0)) (List.range' (nat_lit 0) (nat_lit 255) (nat_lit 1))
    (nat_lit 1)) (nat_lit 256039) = true := by
  quickRfl

theorem d1_end : CFSG.KC.Ord.seedDone (nat_lit 253) (CFSG.KC.Ord.valid3 (nat_lit 64009) LO3)
    (M3 (nat_lit 0)) (nat_lit 256039) = true := by
  quickRfl

theorem d2 : Nat.beq (CFSG.KC.Ord.decRun3 CFSG.KD.BrFi23.P2 (nat_lit 256) (nat_lit 65042) (nat_lit 253)
    (nat_lit 64009) RM3 (M3 (nat_lit 1)) (List.range' (nat_lit 0) (nat_lit 255) (nat_lit 1))
    (nat_lit 1)) (nat_lit 256039) = true := by
  quickRfl

theorem d2_end : CFSG.KC.Ord.seedDone (nat_lit 253) (CFSG.KC.Ord.valid3 (nat_lit 64009) LO3)
    (M3 (nat_lit 1)) (nat_lit 256039) = true := by
  quickRfl

theorem consts3 : CFSG.KC.Ord.consts3OK (nat_lit 253) (nat_lit 9) (nat_lit 64009) LO3 RM3 CI3 ONE3 UP3 =
    true := by
  quickRfl

theorem e253 : CFSG.KC.Fi24Ext.padOK ONE3 E253 = true := by quickRfl

theorem y0pad : CFSG.KC.Fi24Ext.padOK (M3 (nat_lit 0)) Y0 = true := by quickRfl

theorem y1pad : CFSG.KC.Fi24Ext.padOK (M3 (nat_lit 1)) Y1 = true := by quickRfl

end CFSG.KD.Fi24Ext

end
