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

theorem tr8c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x10c0) (nat_lit 0x2d))
    (nat_lit 0x500002b) = true := by
  quickRfl

theorem tr8c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x10ed) (nat_lit 0x2d))
    (nat_lit 0x500002a) = true := by
  quickRfl

theorem tr8c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x111a) (nat_lit 0x2d))
    (nat_lit 0x2000024) = true := by
  quickRfl

theorem tr8c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1147) (nat_lit 0x2d))
    (nat_lit 0x5000026) = true := by
  quickRfl

theorem tr8c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1174) (nat_lit 0x2d))
    (nat_lit 0x100002b) = true := by
  quickRfl

theorem tr8c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x11a1) (nat_lit 0x2d))
    (nat_lit 0x600002f) = true := by
  quickRfl

theorem tr8c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x11ce) (nat_lit 0x2d))
    (nat_lit 0x400002f) = true := by
  quickRfl

theorem tr8c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x11fb) (nat_lit 0x2d))
    (nat_lit 0x5000033) = true := by
  quickRfl

theorem tr8c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1228) (nat_lit 0x2d))
    (nat_lit 0x100002e) = true := by
  quickRfl

theorem tr8c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1255) (nat_lit 0x2d))
    (nat_lit 0x200002c) = true := by
  quickRfl

theorem tr8c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1282) (nat_lit 0x2d))
    (nat_lit 0x3000031) = true := by
  quickRfl

theorem tr8c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x12af) (nat_lit 0x29))
    (nat_lit 0x7000032) = true := by
  quickRfl

theorem tr8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x10c0) (nat_lit 0x218))
    (nat_lit 0x2e000218) = true := by
  have h := tr8c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr8c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr8c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
