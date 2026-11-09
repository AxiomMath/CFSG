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

theorem tr15c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1f68) (nat_lit 0x2d))
    (nat_lit 0x4000027) = true := by
  quickRfl

theorem tr15c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1f95) (nat_lit 0x2d))
    (nat_lit 0x3000028) = true := by
  quickRfl

theorem tr15c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1fc2) (nat_lit 0x2d))
    (nat_lit 0x1000029) = true := by
  quickRfl

theorem tr15c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1fef) (nat_lit 0x2d))
    (nat_lit 0x2000029) = true := by
  quickRfl

theorem tr15c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x201c) (nat_lit 0x2d))
    (nat_lit 0x2000029) = true := by
  quickRfl

theorem tr15c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x2049) (nat_lit 0x2d))
    (nat_lit 0x700002a) = true := by
  quickRfl

theorem tr15c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x2076) (nat_lit 0x2d))
    (nat_lit 0x2000029) = true := by
  quickRfl

theorem tr15c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x20a3) (nat_lit 0x2d))
    (nat_lit 0x3000032) = true := by
  quickRfl

theorem tr15c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x20d0) (nat_lit 0x2d))
    (nat_lit 0x5000032) = true := by
  quickRfl

theorem tr15c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x20fd) (nat_lit 0x2d))
    (nat_lit 0x3000026) = true := by
  quickRfl

theorem tr15c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x212a) (nat_lit 0x2d))
    (nat_lit 0x600002b) = true := by
  quickRfl

theorem tr15c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x2157) (nat_lit 0x25))
    (nat_lit 0x100002c) = true := by
  quickRfl

theorem tr15 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1f68) (nat_lit 0x214))
    (nat_lit 0x270001fe) = true := by
  have h := tr15c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr15c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr15c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
