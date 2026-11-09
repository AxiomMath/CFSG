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

theorem tr12c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1920) (nat_lit 0x2d))
    (nat_lit 0x100002b) = true := by
  quickRfl

theorem tr12c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x194d) (nat_lit 0x2d))
    (nat_lit 0x200002e) = true := by
  quickRfl

theorem tr12c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x197a) (nat_lit 0x2d))
    (nat_lit 0x300002b) = true := by
  quickRfl

theorem tr12c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x19a7) (nat_lit 0x2d))
    (nat_lit 0x600002d) = true := by
  quickRfl

theorem tr12c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x19d4) (nat_lit 0x2d))
    (nat_lit 0x500002a) = true := by
  quickRfl

theorem tr12c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1a01) (nat_lit 0x2d))
    (nat_lit 0x37) = true := by
  quickRfl

theorem tr12c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1a2e) (nat_lit 0x2d))
    (nat_lit 0x1000020) = true := by
  quickRfl

theorem tr12c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1a5b) (nat_lit 0x2d))
    (nat_lit 0x2000035) = true := by
  quickRfl

theorem tr12c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1a88) (nat_lit 0x2d))
    (nat_lit 0x500002e) = true := by
  quickRfl

theorem tr12c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1ab5) (nat_lit 0x2d))
    (nat_lit 0x600002b) = true := by
  quickRfl

theorem tr12c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1ae2) (nat_lit 0x2d))
    (nat_lit 0x5000034) = true := by
  quickRfl

theorem tr12c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1b0f) (nat_lit 0x29))
    (nat_lit 0x2000028) = true := by
  quickRfl

theorem tr12 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1920) (nat_lit 0x218))
    (nat_lit 0x2600021c) = true := by
  have h := tr12c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr12c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr12c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
