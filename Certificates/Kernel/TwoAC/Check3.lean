module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import Certificates.Data.Kernel.TwoAC.Check
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import Certificates.Kernel.TwoAC.Data0
public import Certificates.Kernel.TwoAC.Data1
public import Certificates.Kernel.TwoAC.Data2

#bm_mul4 CFSG.KC.BM.TwoAC cBvA Bv [a] BvA []
#bm_mul4 CFSG.KC.BM.TwoAC cBvB Bv [w2] BvB []
#bm_mul4 CFSG.KC.BM.TwoAC cBinv Binv [Bv] I []
#bm_bool CFSG.KC.BM.TwoAC forest0 (CFSG.KC.BM.TwoAC.forestOK Fb Bv BvA BvB V0 V1 0)
#bm_bool CFSG.KC.BM.TwoAC beta_a (Nat.beq (CFSG.KC.BM.mulS Bv betaA) (CFSG.KC.BM.mulS a (CFSG.KC.BM.mulS Bv CFSG.KC.BM.Seeds.A1.s0)))
#bm_bool CFSG.KC.BM.TwoAC beta_b (Nat.beq (CFSG.KC.BM.mulS Bv betaB) (CFSG.KC.BM.mulS w2 (CFSG.KC.BM.mulS Bv CFSG.KC.BM.Seeds.A1.s0)))
#bm_bool CFSG.KC.BM.TwoAC ker0 (Nat.beq (CFSG.KC.BM.mulS th0 V0) 0)
#bm_bool CFSG.KC.BM.TwoAC ker1 (Nat.beq (CFSG.KC.BM.mulS th1 V1) 0)
#bm_bool CFSG.KC.BM.TwoAC xV0 (Nat.beq (CFSG.KC.BM.rowOf (CFSG.KC.BM.mulS x V0) 0) (CFSG.KC.BM.rowOf V0 1))
#bm_bool CFSG.KC.BM.TwoAC xV1 (Nat.beq (CFSG.KC.BM.rowOf (CFSG.KC.BM.mulS x V1) 0) (CFSG.KC.BM.rowOf V1 1))
#bm_bool CFSG.KC.BM.TwoAC indep (CFSG.KC.BM.TwoAC.rowsNZ V0 V1 7)
