module

public import Certificates.Kernel.HNLocal.XData
public import Certificates.Kernel.HNLocal.TreeData
public import Certificates.Kernel.HNLocal.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
public import Certificates.Kernel.HNLocal.TreeJoin
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNLocal

theorem tr3c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x648) (nat_lit 0x2d))
    (nat_lit 0x6000033) = true := by
  quickRfl

theorem tr3c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x675) (nat_lit 0x2d))
    (nat_lit 0x4000032) = true := by
  quickRfl

theorem tr3c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x6a2) (nat_lit 0x2d))
    (nat_lit 0x2000030) = true := by
  quickRfl

theorem tr3c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x6cf) (nat_lit 0x2d))
    (nat_lit 0x6000038) = true := by
  quickRfl

theorem tr3c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x6fc) (nat_lit 0x2d))
    (nat_lit 0x9000036) = true := by
  quickRfl

theorem tr3c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x729) (nat_lit 0x2d))
    (nat_lit 0x5000036) = true := by
  quickRfl

theorem tr3c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x756) (nat_lit 0x2d))
    (nat_lit 0xb000030) = true := by
  quickRfl

theorem tr3c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x783) (nat_lit 0x2d))
    (nat_lit 0x6000026) = true := by
  quickRfl

theorem tr3c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x7b0) (nat_lit 0x2d))
    (nat_lit 0x4000028) = true := by
  quickRfl

theorem tr3c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x7dd) (nat_lit 0x2d))
    (nat_lit 0x100002e) = true := by
  quickRfl

theorem tr3c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x80a) (nat_lit 0x2d))
    (nat_lit 0x500002e) = true := by
  quickRfl

theorem tr3c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x837) (nat_lit 0x29))
    (nat_lit 0x5000031) = true := by
  quickRfl

theorem tr3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x648) (nat_lit 0x218))
    (nat_lit 0x40000244) = true := by
  have h := tr3c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr3c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr3c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
