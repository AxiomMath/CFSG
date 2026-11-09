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

theorem tr5c0 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xa78) (nat_lit 0x2d))
    (nat_lit 0x700002a) = true := by
  quickRfl

theorem tr5c1 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xaa5) (nat_lit 0x2d))
    (nat_lit 0x7000028) = true := by
  quickRfl

theorem tr5c2 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xad2) (nat_lit 0x2d))
    (nat_lit 0x2000036) = true := by
  quickRfl

theorem tr5c3 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xaff) (nat_lit 0x2d))
    (nat_lit 0x5000037) = true := by
  quickRfl

theorem tr5c4 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xb2c) (nat_lit 0x2d))
    (nat_lit 0x8000034) = true := by
  quickRfl

theorem tr5c5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xb59) (nat_lit 0x2d))
    (nat_lit 0x200002a) = true := by
  quickRfl

theorem tr5c6 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xb86) (nat_lit 0x2d))
    (nat_lit 0x5000033) = true := by
  quickRfl

theorem tr5c7 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xbb3) (nat_lit 0x2d))
    (nat_lit 0x4000037) = true := by
  quickRfl

theorem tr5c8 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xbe0) (nat_lit 0x2d))
    (nat_lit 0x5000032) = true := by
  quickRfl

theorem tr5c9 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xc0d) (nat_lit 0x2d))
    (nat_lit 0x600002a) = true := by
  quickRfl

theorem tr5c10 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xc3a) (nat_lit 0x2d))
    (nat_lit 0x3000031) = true := by
  quickRfl

theorem tr5c11 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xc67) (nat_lit 0x29))
    (nat_lit 0x2000024) = true := by
  quickRfl

theorem tr5 : Nat.beq (CFSG.KC.HNLocal.treeSum XC TD MSF (nat_lit 0x116520) M CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB GFC (nat_lit 0xa78) (nat_lit 0x218))
    (nat_lit 0x38000238) = true := by
  have h := tr5c0
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c1 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c2 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c3 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c4 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c5 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c6 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c7 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c8 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c9 rfl rfl rfl
  have h := CFSG.KC.HNLocal.treeSum_join h tr5c10 rfl rfl rfl
  exact CFSG.KC.HNLocal.treeSum_join h tr5c11 rfl rfl rfl

end CFSG.KD.HNLocal

end
