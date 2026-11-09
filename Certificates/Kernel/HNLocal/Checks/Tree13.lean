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

theorem tr13c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1b38) (nat_lit 0x2d))
    (nat_lit 0x400002e) = true := by
  quickRfl

theorem tr13c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1b65) (nat_lit 0x2d))
    (nat_lit 0x200002e) = true := by
  quickRfl

theorem tr13c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1b92) (nat_lit 0x2d))
    (nat_lit 0x6000043) = true := by
  quickRfl

theorem tr13c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1bbf) (nat_lit 0x2d))
    (nat_lit 0x2000037) = true := by
  quickRfl

theorem tr13c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1bec) (nat_lit 0x2d))
    (nat_lit 0x300002c) = true := by
  quickRfl

theorem tr13c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1c19) (nat_lit 0x2d))
    (nat_lit 0x200002e) = true := by
  quickRfl

theorem tr13c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1c46) (nat_lit 0x2d))
    (nat_lit 0x300002b) = true := by
  quickRfl

theorem tr13c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1c73) (nat_lit 0x2d))
    (nat_lit 0x1000030) = true := by
  quickRfl

theorem tr13c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1ca0) (nat_lit 0x2d))
    (nat_lit 0x3000037) = true := by
  quickRfl

theorem tr13c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1ccd) (nat_lit 0x2d))
    (nat_lit 0x500002f) = true := by
  quickRfl

theorem tr13c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1cfa) (nat_lit 0x2d))
    (nat_lit 0x5000030) = true := by
  quickRfl

theorem tr13c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1d27) (nat_lit 0x29))
    (nat_lit 0x3000030) = true := by
  quickRfl

theorem tr13 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1b38) (nat_lit 0x218))
    (nat_lit 0x27000251) = true := by
  have h := tr13c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr13c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr13c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
