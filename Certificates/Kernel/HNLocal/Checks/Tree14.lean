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

theorem tr14c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1d50) (nat_lit 0x2d))
    (nat_lit 0x400003f) = true := by
  quickRfl

theorem tr14c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1d7d) (nat_lit 0x2d))
    (nat_lit 0x200002f) = true := by
  quickRfl

theorem tr14c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1daa) (nat_lit 0x2d))
    (nat_lit 0x200002e) = true := by
  quickRfl

theorem tr14c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1dd7) (nat_lit 0x2d))
    (nat_lit 0x1000032) = true := by
  quickRfl

theorem tr14c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1e04) (nat_lit 0x2d))
    (nat_lit 0x4000032) = true := by
  quickRfl

theorem tr14c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1e31) (nat_lit 0x2d))
    (nat_lit 0x3000029) = true := by
  quickRfl

theorem tr14c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1e5e) (nat_lit 0x2d))
    (nat_lit 0x400002e) = true := by
  quickRfl

theorem tr14c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1e8b) (nat_lit 0x2d))
    (nat_lit 0x4000034) = true := by
  quickRfl

theorem tr14c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1eb8) (nat_lit 0x2d))
    (nat_lit 0x4000027) = true := by
  quickRfl

theorem tr14c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1ee5) (nat_lit 0x2d))
    (nat_lit 0x7000034) = true := by
  quickRfl

theorem tr14c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1f12) (nat_lit 0x2d))
    (nat_lit 0x3000034) = true := by
  quickRfl

theorem tr14c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1f3f) (nat_lit 0x29))
    (nat_lit 0x4000021) = true := by
  quickRfl

theorem tr14 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1d50) (nat_lit 0x218))
    (nat_lit 0x2a00023b) = true := by
  have h := tr14c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr14c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr14c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
