module

public import Certificates.Kernel.HNChain.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HNChain

open CFSG.KC.HNLocal

@[expose] def lvRoot (i : Nat) : Nat := [0, 11, 12, 13, 14, 15, 16, 17].getD i 0

@[expose] noncomputable def tpOk (i : Nat) : Bool := Nat.beq (GT i) (trM (RB (lvRoot i + 1)))

@[expose] def fxG (n : Nat) : Nat := [0, 1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7].getD n 0
@[expose] def fxV (n : Nat) : Nat := [0, 0, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2].getD n 0

@[expose] noncomputable def fxOk (n : Nat) : Bool :=
  fixVec CFSG.KD.HNLocal.MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.HNLocal.CM3 CFSG.KD.OrdHN.RM
    (GT (fxG n)) (VT (fxV n))

@[expose] noncomputable def actOk (s : Nat) : Bool :=
  actLeaf XC3 (PI s) CFSG.KD.HNLocal.M CFSG.KD.HNLocal.MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H
    CFSG.KD.HNLocal.CM3 CFSG.KD.OrdHN.RM 32 (GT (4 + s)) 0 32

end CFSG.KD.HNChain

#kss_each CFSG.KD.HNChain.tp CFSG.KD.HNChain.tpOk 8
#kss_each CFSG.KD.HNChain.fx CFSG.KD.HNChain.fxOk 18
#kss_each CFSG.KD.HNChain.act CFSG.KD.HNChain.actOk 4

namespace CFSG.KD.HNChain

open CFSG.KC.HNLocal

theorem x0_1 : Nat.beq (recX XC1 CFSG.KD.HNLocal.M 0) V1 = true := by quickRfl
theorem td0_1 : Nat.beq (Nat.land (TD1 0) 0x1fffff) 1 = true := by quickRfl
theorem tdn_1 : Nat.beq (Nat.land (TD1 79) 0x1fffff) 10395 = true := by quickRfl
theorem x0_2 : Nat.beq (recX XC2 CFSG.KD.HNLocal.M 0) V2 = true := by quickRfl
theorem td0_2 : Nat.beq (Nat.land (TD2 0) 0x1fffff) 1 = true := by quickRfl
theorem tdn_2 : Nat.beq (Nat.land (TD2 6) 0x1fffff) 720 = true := by quickRfl
theorem x0_3 : Nat.beq (recX XC3 CFSG.KD.HNLocal.M 0) V3 = true := by quickRfl
theorem so3 : sortLeaf XC3 SD3 32 CFSG.KD.HNLocal.M 0 = true := by quickRfl

end CFSG.KD.HNChain

end
