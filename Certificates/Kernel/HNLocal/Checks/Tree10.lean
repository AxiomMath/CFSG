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

theorem tr10c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x14f0) (nat_lit 0x2d))
    (nat_lit 0x400002f) = true := by
  quickRfl

theorem tr10c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x151d) (nat_lit 0x2d))
    (nat_lit 0x300002b) = true := by
  quickRfl

theorem tr10c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x154a) (nat_lit 0x2d))
    (nat_lit 0x6000029) = true := by
  quickRfl

theorem tr10c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1577) (nat_lit 0x2d))
    (nat_lit 0x400002a) = true := by
  quickRfl

theorem tr10c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x15a4) (nat_lit 0x2d))
    (nat_lit 0x600002e) = true := by
  quickRfl

theorem tr10c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x15d1) (nat_lit 0x2d))
    (nat_lit 0x600002a) = true := by
  quickRfl

theorem tr10c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x15fe) (nat_lit 0x2d))
    (nat_lit 0x2000037) = true := by
  quickRfl

theorem tr10c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x162b) (nat_lit 0x2d))
    (nat_lit 0x1000023) = true := by
  quickRfl

theorem tr10c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1658) (nat_lit 0x2d))
    (nat_lit 0x400002a) = true := by
  quickRfl

theorem tr10c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x1685) (nat_lit 0x2d))
    (nat_lit 0x1000029) = true := by
  quickRfl

theorem tr10c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x16b2) (nat_lit 0x2d))
    (nat_lit 0x7000038) = true := by
  quickRfl

theorem tr10c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x16df) (nat_lit 0x29))
    (nat_lit 0x100002b) = true := by
  quickRfl

theorem tr10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x14f0) (nat_lit 0x218))
    (nat_lit 0x2d000215) = true := by
  have h := tr10c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr10c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr10c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
