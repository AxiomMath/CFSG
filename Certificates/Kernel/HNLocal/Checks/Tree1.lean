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

theorem tr1c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x218) (nat_lit 0x2d))
    (nat_lit 0x7000034) = true := by
  quickRfl

theorem tr1c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x245) (nat_lit 0x2d))
    (nat_lit 0xa000027) = true := by
  quickRfl

theorem tr1c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x272) (nat_lit 0x2d))
    (nat_lit 0x400002a) = true := by
  quickRfl

theorem tr1c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x29f) (nat_lit 0x2d))
    (nat_lit 0x6000035) = true := by
  quickRfl

theorem tr1c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x2cc) (nat_lit 0x2d))
    (nat_lit 0x500003b) = true := by
  quickRfl

theorem tr1c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x2f9) (nat_lit 0x2d))
    (nat_lit 0x3000029) = true := by
  quickRfl

theorem tr1c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x326) (nat_lit 0x2d))
    (nat_lit 0x4000027) = true := by
  quickRfl

theorem tr1c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x353) (nat_lit 0x2d))
    (nat_lit 0x5000028) = true := by
  quickRfl

theorem tr1c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x380) (nat_lit 0x2d))
    (nat_lit 0x4000031) = true := by
  quickRfl

theorem tr1c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x3ad) (nat_lit 0x2d))
    (nat_lit 0x200002a) = true := by
  quickRfl

theorem tr1c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x3da) (nat_lit 0x2d))
    (nat_lit 0x700002a) = true := by
  quickRfl

theorem tr1c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x407) (nat_lit 0x29))
    (nat_lit 0x6000032) = true := by
  quickRfl

theorem tr1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0x218) (nat_lit 0x218))
    (nat_lit 0x3f000224) = true := by
  have h := tr1c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr1c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr1c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
