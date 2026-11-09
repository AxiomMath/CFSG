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

theorem tr11c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1708) (nat_lit 0x2d))
    (nat_lit 0x7000023) = true := by
  quickRfl

theorem tr11c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1735) (nat_lit 0x2d))
    (nat_lit 0x4000036) = true := by
  quickRfl

theorem tr11c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1762) (nat_lit 0x2d))
    (nat_lit 0x200002a) = true := by
  quickRfl

theorem tr11c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x178f) (nat_lit 0x2d))
    (nat_lit 0x3000036) = true := by
  quickRfl

theorem tr11c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x17bc) (nat_lit 0x2d))
    (nat_lit 0x3000036) = true := by
  quickRfl

theorem tr11c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x17e9) (nat_lit 0x2d))
    (nat_lit 0x2000041) = true := by
  quickRfl

theorem tr11c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1816) (nat_lit 0x2d))
    (nat_lit 0x300002a) = true := by
  quickRfl

theorem tr11c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1843) (nat_lit 0x2d))
    (nat_lit 0x100002b) = true := by
  quickRfl

theorem tr11c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1870) (nat_lit 0x2d))
    (nat_lit 0x5000034) = true := by
  quickRfl

theorem tr11c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x189d) (nat_lit 0x2d))
    (nat_lit 0x200002c) = true := by
  quickRfl

theorem tr11c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x18ca) (nat_lit 0x2d))
    (nat_lit 0x5000024) = true := by
  quickRfl

theorem tr11c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x18f7) (nat_lit 0x29))
    (nat_lit 0x200002d) = true := by
  quickRfl

theorem tr11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1708) (nat_lit 0x218))
    (nat_lit 0x27000236) = true := by
  have h := tr11c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr11c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr11c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
