module

public import Certificates.Kernel.HNLocal.XData
public import Certificates.Kernel.HNLocal.TreeData
public import Certificates.Kernel.HNLocal.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

theorem td0 : Nat.beq (Nat.land (TD (nat_lit 0x0)) (nat_lit 0x1fffff)) (nat_lit 0x1) = true := by
  quickRfl

theorem tdn : Nat.beq (Nat.land (TD (nat_lit 0x217c)) (nat_lit 0x1fffff)) (nat_lit 0x116520) =
    true := by
  quickRfl

theorem masks : CFSG.KC.HNLocal.masksOK MS = true := by quickRfl

theorem cm : CFSG.KC.HNLocal.cmOK CM3 M = true := by quickRfl

theorem tp_GA : Nat.beq GA (CFSG.KC.HNLocal.trM (RB (nat_lit 0x1))) = true := by quickRfl

theorem tp_GB : Nat.beq GB (CFSG.KC.HNLocal.trM (RB (nat_lit 0x2))) = true := by quickRfl

theorem tp_GX2 : Nat.beq GX2 (CFSG.KC.HNLocal.trM (RB (nat_lit 0x3))) = true := by quickRfl

theorem tp_GX3 : Nat.beq GX3 (CFSG.KC.HNLocal.trM (RB (nat_lit 0x4))) = true := by quickRfl

theorem tp_GT2 : Nat.beq GT2 (CFSG.KC.HNLocal.trM (RB (nat_lit 0xd))) = true := by quickRfl

theorem tp_GT4 : Nat.beq GT4 (CFSG.KC.HNLocal.trM (RB (nat_lit 0xe))) = true := by quickRfl

theorem msf : CFSG.KC.HNLocal.msfOK MS MSF = true := by quickRfl

theorem tp_GFC : Nat.beq GFC (CFSG.KC.HNLocal.trM LC) = true := by quickRfl

theorem v_LC : vld LC = true := by quickRfl

theorem v_PF2 : vld PF2 = true := by quickRfl

theorem v_QF2 : vld QF2 = true := by quickRfl

theorem v_PF4 : vld PF4 = true := by quickRfl

theorem v_QF4 : vld QF4 = true := by quickRfl

theorem pf2 : Nat.beq (mul PF2 (CFSG.KC.Ord.redP (nat_lit 0xd) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H
    (nat_lit 0x5) (nat_lit 0x9) (Nat.add (RB (nat_lit 0xd)) (Nat.mul (nat_lit 0x4) CFSG.KD.OrdHN.ONE))))
    (Nat.land LC (Nat.sub (Nat.shiftLeft (nat_lit 0x1) (nat_lit 0x17a38)) (nat_lit 0x1))) = true := by
  quickRfl

theorem qf2 : Nat.beq (mul QF2 (Nat.land LC (Nat.sub (Nat.shiftLeft (nat_lit 0x1) (nat_lit 0x17a38))
    (nat_lit 0x1)))) (CFSG.KC.Ord.redP (nat_lit 0xd) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H (nat_lit 0x5)
    (nat_lit 0x9) (Nat.add (RB (nat_lit 0xd)) (Nat.mul (nat_lit 0x4) CFSG.KD.OrdHN.ONE))) = true := by
  quickRfl

theorem pf4 : Nat.beq (mul PF4 (CFSG.KC.Ord.redP (nat_lit 0xd) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H
    (nat_lit 0x5) (nat_lit 0x9) (Nat.add (RB (nat_lit 0xe)) (Nat.mul (nat_lit 0x4) CFSG.KD.OrdHN.ONE))))
    (Nat.land (Nat.shiftRight LC (nat_lit 0x17a38))
      (Nat.sub (Nat.shiftLeft (nat_lit 0x1) (nat_lit 0x1b040)) (nat_lit 0x1))) = true := by
  quickRfl

theorem qf4 : Nat.beq (mul QF4 (Nat.land (Nat.shiftRight LC (nat_lit 0x17a38))
    (Nat.sub (Nat.shiftLeft (nat_lit 0x1) (nat_lit 0x1b040)) (nat_lit 0x1))))
    (CFSG.KC.Ord.redP (nat_lit 0xd) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H (nat_lit 0x5) (nat_lit 0x9)
      (Nat.add (RB (nat_lit 0xe)) (Nat.mul (nat_lit 0x4) CFSG.KD.OrdHN.ONE))) = true := by
  quickRfl

theorem w14 : Nat.beq (RB (nat_lit 0xf)) (RB (nat_lit 0x3)) = true := by quickRfl

theorem t2sq : Nat.beq (mul (RB (nat_lit 0xd)) (RB (nat_lit 0xd))) CFSG.KD.OrdHN.ONE = true := by
  quickRfl

theorem t2ne : CFSG.KC.Ord.notB (Nat.beq (RB (nat_lit 0xd)) CFSG.KD.OrdHN.ONE) = true := by quickRfl

theorem t4sq : Nat.beq (mul (RB (nat_lit 0xe)) (RB (nat_lit 0xe))) CFSG.KD.OrdHN.ONE = true := by
  quickRfl

theorem t4ne : CFSG.KC.Ord.notB (Nat.beq (RB (nat_lit 0xe)) CFSG.KD.OrdHN.ONE) = true := by quickRfl

theorem trc2 : Nat.beq (CFSG.KC.HNLocal.traceL (RB (nat_lit 0xd))) (nat_lit 0x1) = true := by
  quickRfl

theorem trc4 : Nat.beq (CFSG.KC.HNLocal.traceL (RB (nat_lit 0xe))) (nat_lit 0x0) = true := by
  quickRfl

theorem w_GX2_0 : CFSG.KC.HNLocal.actLeaf WC PI2 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GX2 (nat_lit 0x0) (nat_lit 0x85) = true := by quickRfl

theorem w_GX2_1 : CFSG.KC.HNLocal.actLeaf WC PI2 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GX2 (nat_lit 0x1) (nat_lit 0x85) = true := by quickRfl

theorem w_GX2_2 : CFSG.KC.HNLocal.actLeaf WC PI2 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GX2 (nat_lit 0x2) (nat_lit 0x85) = true := by quickRfl

theorem w_GX2_3 : CFSG.KC.HNLocal.actLeaf WC PI2 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GX2 (nat_lit 0x3) (nat_lit 0x3f) = true := by quickRfl

theorem v0_GX2 : CFSG.KC.HNLocal.fixVec MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GX2
    V0 = true := by quickRfl

theorem w_GX3_0 : CFSG.KC.HNLocal.actLeaf WC PI3 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GX3 (nat_lit 0x0) (nat_lit 0x85) = true := by quickRfl

theorem w_GX3_1 : CFSG.KC.HNLocal.actLeaf WC PI3 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GX3 (nat_lit 0x1) (nat_lit 0x85) = true := by quickRfl

theorem w_GX3_2 : CFSG.KC.HNLocal.actLeaf WC PI3 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GX3 (nat_lit 0x2) (nat_lit 0x85) = true := by quickRfl

theorem w_GX3_3 : CFSG.KC.HNLocal.actLeaf WC PI3 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GX3 (nat_lit 0x3) (nat_lit 0x3f) = true := by quickRfl

theorem v0_GX3 : CFSG.KC.HNLocal.fixVec MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GX3
    V0 = true := by quickRfl

theorem w_GT2_0 : CFSG.KC.HNLocal.actLeaf WC PT2 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GT2 (nat_lit 0x0) (nat_lit 0x85) = true := by quickRfl

theorem w_GT2_1 : CFSG.KC.HNLocal.actLeaf WC PT2 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GT2 (nat_lit 0x1) (nat_lit 0x85) = true := by quickRfl

theorem w_GT2_2 : CFSG.KC.HNLocal.actLeaf WC PT2 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GT2 (nat_lit 0x2) (nat_lit 0x85) = true := by quickRfl

theorem w_GT2_3 : CFSG.KC.HNLocal.actLeaf WC PT2 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GT2 (nat_lit 0x3) (nat_lit 0x3f) = true := by quickRfl

theorem v0_GT2 : CFSG.KC.HNLocal.fixVec MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GT2
    V0 = true := by quickRfl

theorem w_GT4_0 : CFSG.KC.HNLocal.actLeaf WC PT4 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GT4 (nat_lit 0x0) (nat_lit 0x85) = true := by quickRfl

theorem w_GT4_1 : CFSG.KC.HNLocal.actLeaf WC PT4 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GT4 (nat_lit 0x1) (nat_lit 0x85) = true := by quickRfl

theorem w_GT4_2 : CFSG.KC.HNLocal.actLeaf WC PT4 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GT4 (nat_lit 0x2) (nat_lit 0x85) = true := by quickRfl

theorem w_GT4_3 : CFSG.KC.HNLocal.actLeaf WC PT4 M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
    CFSG.KD.OrdHN.RM (nat_lit 0x1ce) GT4 (nat_lit 0x3) (nat_lit 0x3f) = true := by quickRfl

theorem v0_GT4 : CFSG.KC.HNLocal.fixVec MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GT4
    V0 = true := by quickRfl

theorem x0 : Nat.beq (CFSG.KC.HNLocal.recX XC M (nat_lit 0x0)) V0 = true := by quickRfl

theorem wsort : CFSG.KC.HNLocal.sortLeaf WC SW (nat_lit 0x1ce) M (nat_lit 0x0) = true := by quickRfl

theorem wsort1 : CFSG.KC.HNLocal.sortLeaf WC SW (nat_lit 0x1ce) M (nat_lit 0x1) = true := by quickRfl

theorem wsort2 : CFSG.KC.HNLocal.sortLeaf WC SW (nat_lit 0x1ce) M (nat_lit 0x2) = true := by quickRfl

theorem wsort3 : CFSG.KC.HNLocal.sortLeaf WC SW (nat_lit 0x1ce) M (nat_lit 0x3) = true := by quickRfl

end CFSG.KD.HNLocal

end
