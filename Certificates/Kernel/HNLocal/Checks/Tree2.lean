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

theorem tr2c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x430) (nat_lit 0x2d))
    (nat_lit 0x7000032) = true := by
  quickRfl

theorem tr2c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x45d) (nat_lit 0x2d))
    (nat_lit 0x1000024) = true := by
  quickRfl

theorem tr2c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x48a) (nat_lit 0x2d))
    (nat_lit 0x5000035) = true := by
  quickRfl

theorem tr2c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x4b7) (nat_lit 0x2d))
    (nat_lit 0x3000037) = true := by
  quickRfl

theorem tr2c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x4e4) (nat_lit 0x2d))
    (nat_lit 0x1000020) = true := by
  quickRfl

theorem tr2c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x511) (nat_lit 0x2d))
    (nat_lit 0x5000032) = true := by
  quickRfl

theorem tr2c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x53e) (nat_lit 0x2d))
    (nat_lit 0x3000031) = true := by
  quickRfl

theorem tr2c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x56b) (nat_lit 0x2d))
    (nat_lit 0x2000026) = true := by
  quickRfl

theorem tr2c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x598) (nat_lit 0x2d))
    (nat_lit 0x6000031) = true := by
  quickRfl

theorem tr2c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x5c5) (nat_lit 0x2d))
    (nat_lit 0x400002e) = true := by
  quickRfl

theorem tr2c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x5f2) (nat_lit 0x2d))
    (nat_lit 0x500002a) = true := by
  quickRfl

theorem tr2c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x61f) (nat_lit 0x29))
    (nat_lit 0x5000028) = true := by
  quickRfl

theorem tr2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x430) (nat_lit 0x218))
    (nat_lit 0x2f00021c) = true := by
  have h := tr2c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr2c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr2c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
