module

public import Certificates.Kernel.HNChain.Data
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHNChain

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KD.HNChain

theorem neg_tree : Bool.not (Nat.blt (treeLeaf XC1 TD1 CFSG.KD.HNLocal.MSF 10395 CFSG.KD.HNLocal.M
    CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.HNLocal.CM3 CFSG.KD.OrdHN.RM G11 G10 CFSG.KD.OrdHN.ONE 0)
    (2 ^ 50)) = true := by quickRfl

theorem neg_sort : Bool.not (sortLeaf XC1 SD2 10395 CFSG.KD.HNLocal.M 0) = true := by quickRfl

theorem neg_fix : Bool.not (fixVec CFSG.KD.HNLocal.MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H
    CFSG.KD.HNLocal.CM3 CFSG.KD.OrdHN.RM G20 V2) = true := by quickRfl

theorem neg_act : Bool.not (actLeaf XC3 (PI 1) CFSG.KD.HNLocal.M CFSG.KD.HNLocal.MS CFSG.KD.OrdHN.L
    CFSG.KD.OrdHN.H CFSG.KD.HNLocal.CM3 CFSG.KD.OrdHN.RM 32 G30 0 32) = true := by quickRfl

theorem neg_x0 : Bool.not (Nat.beq (recX XC1 CFSG.KD.HNLocal.M 0) V2) = true := by quickRfl

theorem neg_rel : Bool.not (CFSG.KC.HNMult.relW RB CFSG.KD.HNLocal.mul 18 CFSG.KD.OrdHN.ONE [1]) =
    true := by quickRfl

end CertificateChecks.KernelHNChain

end
