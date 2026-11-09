module

public import Certificates.Kernel.HNLocal.ZData
public import Certificates.Kernel.HNLocal.Checks.Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.HNLocalZ

#kc_each CFSG.KD.HNLocalZ.zRel 1 4

theorem zRel0_0 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x0) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel0_1 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x1) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel0_2 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x2) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel0_3 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x3) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel0_4 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x4) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel0_5 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x5) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel0_6 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x6) (nat_lit 0x5) = true := by
  quickRfl

theorem zRel0_7 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0xb) (nat_lit 0x5) = true := by
  quickRfl

theorem zRel0 : zRel 0 = true := by
  have h := (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of zRel0_0 zRel0_1) zRel0_2) zRel0_3) zRel0_4) zRel0_5) zRel0_6) zRel0_7)
  exact h

end CFSG.KD.HNLocalZ

end
