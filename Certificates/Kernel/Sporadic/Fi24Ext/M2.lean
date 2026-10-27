module

public import Certificates.Kernel.Sporadic.Fi24Ext.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24Ext

theorem u2 : Nat.beq (CFSG.KD.BrFi24.MUL U U) U2 = true := by quickRfl

theorem u4 : Nat.beq (CFSG.KD.BrFi24.MUL U2 U2) U4 = true := by quickRfl

theorem u8 : Nat.beq (CFSG.KD.BrFi24.MUL U4 U4) U8 = true := by quickRfl

theorem u16 : Nat.beq (CFSG.KD.BrFi24.MUL U8 U8) U16 = true := by quickRfl

theorem h0 : Nat.beq (CFSG.KD.BrFi24.MUL U16 (CFSG.KD.BrFi24.MUL U8 (CFSG.KD.BrFi24.MUL U4 U2))) H0 =
    true := by quickRfl

theorem y2 : Nat.beq (CFSG.KD.BrFi24.MUL Yw Yw) Y2 = true := by quickRfl

theorem y4 : Nat.beq (CFSG.KD.BrFi24.MUL Y2 Y2) Y4 = true := by quickRfl

theorem h1 : Nat.beq (CFSG.KD.BrFi24.MUL Xw (CFSG.KD.BrFi24.MUL Y4 X2w)) H1 = true := by quickRfl

theorem x0 : Nat.beq (CFSG.KD.BrFi24.MUL SRF (CFSG.KD.BrFi24.MUL H0 CFSG.KD.Fi24Fix.R)) X0 = true := by
  quickRfl

theorem x1 : Nat.beq (CFSG.KD.BrFi24.MUL SRF (CFSG.KD.BrFi24.MUL H1 CFSG.KD.Fi24Fix.R)) X1 = true := by
  quickRfl

theorem l0 : Nat.beq (CFSG.KD.BrFi24.MUL X0 Q) (CFSG.KD.BrFi24.MUL Q Y0) = true := by quickRfl

theorem l1 : Nat.beq (CFSG.KD.BrFi24.MUL X1 Q) (CFSG.KD.BrFi24.MUL Q Y1) = true := by quickRfl

theorem qiq : Nat.beq (CFSG.KD.BrFi24.MUL Qi Q) E253 = true := by quickRfl

theorem qqi : Nat.beq (CFSG.KD.BrFi24.MUL Q Qi) E253 = true := by quickRfl

theorem eqi : Nat.beq (CFSG.KD.BrFi24.MUL E253 Qi) Qi = true := by quickRfl

theorem qie : Nat.beq (CFSG.KD.BrFi24.MUL Qi E253) Qi = true := by quickRfl

end CFSG.KD.Fi24Ext

end
