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

theorem tr9c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x12d8) (nat_lit 0x2d))
    (nat_lit 0x4000034) = true := by
  quickRfl

theorem tr9c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1305) (nat_lit 0x2d))
    (nat_lit 0x3000032) = true := by
  quickRfl

theorem tr9c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1332) (nat_lit 0x2d))
    (nat_lit 0x3000030) = true := by
  quickRfl

theorem tr9c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x135f) (nat_lit 0x2d))
    (nat_lit 0x7000022) = true := by
  quickRfl

theorem tr9c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x138c) (nat_lit 0x2d))
    (nat_lit 0x1000031) = true := by
  quickRfl

theorem tr9c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x13b9) (nat_lit 0x2d))
    (nat_lit 0x4000037) = true := by
  quickRfl

theorem tr9c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x13e6) (nat_lit 0x2d))
    (nat_lit 0x3000034) = true := by
  quickRfl

theorem tr9c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1413) (nat_lit 0x2d))
    (nat_lit 0x2000029) = true := by
  quickRfl

theorem tr9c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1440) (nat_lit 0x2d))
    (nat_lit 0x4000031) = true := by
  quickRfl

theorem tr9c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x146d) (nat_lit 0x2d))
    (nat_lit 0x1000029) = true := by
  quickRfl

theorem tr9c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x149a) (nat_lit 0x2d))
    (nat_lit 0x7000036) = true := by
  quickRfl

theorem tr9c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x14c7) (nat_lit 0x29))
    (nat_lit 0x5000023) = true := by
  quickRfl

theorem tr9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x12d8) (nat_lit 0x218))
    (nat_lit 0x2c000230) = true := by
  have h := tr9c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr9c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr9c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
