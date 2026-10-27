module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import Certificates.Data.Kernel.TwoAC.Check
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import Certificates.Kernel.TwoAC.Data0
public import Certificates.Kernel.TwoAC.Data2
public import Certificates.Kernel.TwoAC.Data4

#bm_mul4 CFSG.KC.BM.TwoAC cS4A S4 [a] S4A []
#bm_mul4 CFSG.KC.BM.TwoAC cS4B S4 [w2] S4B []
#bm_mul4 CFSG.KC.BM.TwoAC cS5A S5 [a] S5A []
#bm_mul4 CFSG.KC.BM.TwoAC cS5B S5 [w2] S5B []
#bm_mul4 CFSG.KC.BM.TwoAC cS6A S6 [a] S6A []
#bm_mul4 CFSG.KC.BM.TwoAC cS6B S6 [w2] S6B []
#bm_bool CFSG.KC.BM.TwoAC forest4 (CFSG.KC.BM.TwoAC.forestOK Fb S4 S4A S4B V0 V1 4)
#bm_bool CFSG.KC.BM.TwoAC forest5 (CFSG.KC.BM.TwoAC.forestOK Fb S5 S5A S5B V0 V1 5)
#bm_bool CFSG.KC.BM.TwoAC forest6 (CFSG.KC.BM.TwoAC.forestOK Fb S6 S6A S6B V0 V1 6)
#bm_bool CFSG.KC.BM.TwoAC tests (CFSG.KC.BM.TwoAC.combNZ [(CFSG.KC.BM.TwoAC.testN S4 a w2 CFSG.KC.BM.Seeds.A1.s0 betaA betaB) (CFSG.KC.BM.TwoAC.testN S5 a w2 CFSG.KC.BM.Seeds.A1.s0 betaA betaB) (CFSG.KC.BM.TwoAC.testN S6 a w2 CFSG.KC.BM.Seeds.A1.s0 betaA betaB)])
