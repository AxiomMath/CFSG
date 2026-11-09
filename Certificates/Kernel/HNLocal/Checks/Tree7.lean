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

theorem tr7c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xea8) (nat_lit 0x2d))
    (nat_lit 0xa00002e) = true := by
  quickRfl

theorem tr7c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xed5) (nat_lit 0x2d))
    (nat_lit 0x3000029) = true := by
  quickRfl

theorem tr7c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xf02) (nat_lit 0x2d))
    (nat_lit 0x7000036) = true := by
  quickRfl

theorem tr7c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xf2f) (nat_lit 0x2d))
    (nat_lit 0x4000025) = true := by
  quickRfl

theorem tr7c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xf5c) (nat_lit 0x2d))
    (nat_lit 0x7000026) = true := by
  quickRfl

theorem tr7c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xf89) (nat_lit 0x2d))
    (nat_lit 0x600002a) = true := by
  quickRfl

theorem tr7c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xfb6) (nat_lit 0x2d))
    (nat_lit 0x300001c) = true := by
  quickRfl

theorem tr7c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xfe3) (nat_lit 0x2d))
    (nat_lit 0x3000029) = true := by
  quickRfl

theorem tr7c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1010) (nat_lit 0x2d))
    (nat_lit 0x200002d) = true := by
  quickRfl

theorem tr7c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x103d) (nat_lit 0x2d))
    (nat_lit 0x2000034) = true := by
  quickRfl

theorem tr7c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x106a) (nat_lit 0x2d))
    (nat_lit 0x3000027) = true := by
  quickRfl

theorem tr7c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1097) (nat_lit 0x29))
    (nat_lit 0x4000026) = true := by
  quickRfl

theorem tr7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xea8) (nat_lit 0x218))
    (nat_lit 0x360001f5) = true := by
  have h := tr7c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr7c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr7c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
