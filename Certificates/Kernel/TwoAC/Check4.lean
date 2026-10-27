module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import Certificates.Data.Kernel.TwoAC.Check
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import Certificates.Kernel.TwoAC.Data0
public import Certificates.Kernel.TwoAC.Data2
public import Certificates.Kernel.TwoAC.Data3

#bm_mul4 CFSG.KC.BM.TwoAC cS2A S2 [a] S2A []
#bm_mul4 CFSG.KC.BM.TwoAC cS2B S2 [w2] S2B []
#bm_mul4 CFSG.KC.BM.TwoAC cS3A S3 [a] S3A []
#bm_mul4 CFSG.KC.BM.TwoAC cS3B S3 [w2] S3B []
#bm_bool CFSG.KC.BM.TwoAC forest2 (CFSG.KC.BM.TwoAC.forestOK Fb S2 S2A S2B V0 V1 2)
#bm_bool CFSG.KC.BM.TwoAC forest3 (CFSG.KC.BM.TwoAC.forestOK Fb S3 S3A S3B V0 V1 3)
#bm_bool CFSG.KC.BM.TwoAC test2 (Nat.beq (CFSG.KC.BM.TwoAC.testN S2 a w2 CFSG.KC.BM.Seeds.A1.s0 betaA betaB) 0)
#bm_bool CFSG.KC.BM.TwoAC test3 (Nat.beq (CFSG.KC.BM.TwoAC.testN S3 a w2 CFSG.KC.BM.Seeds.A1.s0 betaA betaB) 0)
#bm_mul4 CFSG.KC.BM.TwoAC cP2 P2 [S2] Q2 []
#bm_mul4 CFSG.KC.BM.TwoAC cP3 P3 [S3] Q3 []
#bm_bool CFSG.KC.BM.TwoAC shape2 (CFSG.KC.BM.shapeOK Q2 1)
#bm_bool CFSG.KC.BM.TwoAC ech2 (CFSG.KC.BM.echFrom P2 1)
#bm_bool CFSG.KC.BM.TwoAC shape3 (CFSG.KC.BM.shapeOK Q3 78)
#bm_bool CFSG.KC.BM.TwoAC ech3 (CFSG.KC.BM.echFrom P3 78)
