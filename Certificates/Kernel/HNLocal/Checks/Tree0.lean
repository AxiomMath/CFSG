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

theorem tr0c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x0) (nat_lit 0x2d))
    (nat_lit 0xc000036) = true := by
  quickRfl

theorem tr0c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x2d) (nat_lit 0x2d))
    (nat_lit 0x5000022) = true := by
  quickRfl

theorem tr0c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x5a) (nat_lit 0x2d))
    (nat_lit 0x300002b) = true := by
  quickRfl

theorem tr0c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x87) (nat_lit 0x2d))
    (nat_lit 0x300002f) = true := by
  quickRfl

theorem tr0c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xb4) (nat_lit 0x2d))
    (nat_lit 0x5000025) = true := by
  quickRfl

theorem tr0c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xe1) (nat_lit 0x2d))
    (nat_lit 0x300002d) = true := by
  quickRfl

theorem tr0c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x10e) (nat_lit 0x2d))
    (nat_lit 0x300002f) = true := by
  quickRfl

theorem tr0c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x13b) (nat_lit 0x2d))
    (nat_lit 0x2000028) = true := by
  quickRfl

theorem tr0c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x168) (nat_lit 0x2d))
    (nat_lit 0x700002b) = true := by
  quickRfl

theorem tr0c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x195) (nat_lit 0x2d))
    (nat_lit 0x5000031) = true := by
  quickRfl

theorem tr0c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1c2) (nat_lit 0x2d))
    (nat_lit 0x100002a) = true := by
  quickRfl

theorem tr0c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1ef) (nat_lit 0x29))
    (nat_lit 0x400002e) = true := by
  quickRfl

theorem tr0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x0) (nat_lit 0x218))
    (nat_lit 0x3500020f) = true := by
  have h := tr0c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr0c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr0c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
