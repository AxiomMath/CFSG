module

public import Certificates.Kernel.HNChain.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HNChain

theorem roots : CFSG.KC.Ord.rootsOK RB CFSG.KD.HNLocal.vld 1 19 = true := by quickRfl

theorem invs : CFSG.KC.Ord.invsOK RB CFSG.KD.HNLocal.mul CFSG.KD.HNLocal.vld 18
    CFSG.KD.OrdHN.ONE = true := by quickRfl

theorem rws : CFSG.KC.HNMult.relWRange RB CFSG.KD.HNLocal.mul 18 CFSG.KD.OrdHN.ONE WDL 0 16 =
    true := by quickRfl

theorem ra : Nat.beq (RB 1) (CFSG.KD.OrdHN.RW 1) = true := by quickRfl

theorem rb : Nat.beq (RB 2) (CFSG.KD.OrdHN.RW 2) = true := by quickRfl

end CFSG.KD.HNChain

end
