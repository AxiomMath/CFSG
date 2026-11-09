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

#kc_each CFSG.KD.HNLocalZ.zRel 5 8

theorem zRel4_0 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x40) (nat_lit 0x6) = true := by
  quickRfl

theorem zRel4_1 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x46) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel4_2 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x47) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel4_3 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x48) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel4_4 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x49) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel4_5 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x4a) (nat_lit 0x1) = true := by
  quickRfl

theorem zRel4_6 : CFSG.KC.HNMult.relWRange RZ CFSG.KD.HNLocal.mul (nat_lit 0x56) CFSG.KD.OrdHN.ONE
    WZL (nat_lit 0x4b) (nat_lit 0x5) = true := by
  quickRfl

theorem zRel4 : zRel 4 = true := by
  have h := (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of (CFSG.KD.HNLocal.relWRange_of zRel4_0 zRel4_1) zRel4_2) zRel4_3) zRel4_4) zRel4_5) zRel4_6)
  exact h

end CFSG.KD.HNLocalZ

end
