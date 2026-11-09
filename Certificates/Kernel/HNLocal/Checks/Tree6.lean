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

theorem tr6c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xc90) (nat_lit 0x2d))
    (nat_lit 0x300002e) = true := by
  quickRfl

theorem tr6c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xcbd) (nat_lit 0x2d))
    (nat_lit 0x4000027) = true := by
  quickRfl

theorem tr6c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xcea) (nat_lit 0x2d))
    (nat_lit 0x400003e) = true := by
  quickRfl

theorem tr6c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xd17) (nat_lit 0x2d))
    (nat_lit 0x1000026) = true := by
  quickRfl

theorem tr6c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xd44) (nat_lit 0x2d))
    (nat_lit 0x2000036) = true := by
  quickRfl

theorem tr6c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xd71) (nat_lit 0x2d))
    (nat_lit 0x3000021) = true := by
  quickRfl

theorem tr6c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xd9e) (nat_lit 0x2d))
    (nat_lit 0x6000029) = true := by
  quickRfl

theorem tr6c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xdcb) (nat_lit 0x2d))
    (nat_lit 0x300002c) = true := by
  quickRfl

theorem tr6c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xdf8) (nat_lit 0x2d))
    (nat_lit 0x8000034) = true := by
  quickRfl

theorem tr6c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xe25) (nat_lit 0x2d))
    (nat_lit 0x2000036) = true := by
  quickRfl

theorem tr6c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xe52) (nat_lit 0x2d))
    (nat_lit 0x4000033) = true := by
  quickRfl

theorem tr6c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xe7f) (nat_lit 0x29))
    (nat_lit 0x3000028) = true := by
  quickRfl

theorem tr6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xc90) (nat_lit 0x218))
    (nat_lit 0x2b00022a) = true := by
  have h := tr6c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr6c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr6c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
