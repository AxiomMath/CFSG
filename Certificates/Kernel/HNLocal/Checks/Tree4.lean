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

theorem tr4c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x860) (nat_lit 0x2d))
    (nat_lit 0x7000028) = true := by
  quickRfl

theorem tr4c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x88d) (nat_lit 0x2d))
    (nat_lit 0x600002c) = true := by
  quickRfl

theorem tr4c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x8ba) (nat_lit 0x2d))
    (nat_lit 0xe00003c) = true := by
  quickRfl

theorem tr4c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x8e7) (nat_lit 0x2d))
    (nat_lit 0x500003b) = true := by
  quickRfl

theorem tr4c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x914) (nat_lit 0x2d))
    (nat_lit 0x700002e) = true := by
  quickRfl

theorem tr4c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x941) (nat_lit 0x2d))
    (nat_lit 0x7000031) = true := by
  quickRfl

theorem tr4c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x96e) (nat_lit 0x2d))
    (nat_lit 0x7000030) = true := by
  quickRfl

theorem tr4c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x99b) (nat_lit 0x2d))
    (nat_lit 0x7000038) = true := by
  quickRfl

theorem tr4c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x9c8) (nat_lit 0x2d))
    (nat_lit 0x600002e) = true := by
  quickRfl

theorem tr4c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x9f5) (nat_lit 0x2d))
    (nat_lit 0x8000026) = true := by
  quickRfl

theorem tr4c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xa22) (nat_lit 0x2d))
    (nat_lit 0x800002b) = true := by
  quickRfl

theorem tr4c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xa4f) (nat_lit 0x29))
    (nat_lit 0x600002c) = true := by
  quickRfl

theorem tr4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x860) (nat_lit 0x218))
    (nat_lit 0x5800023d) = true := by
  have h := tr4c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr4c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr4c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
