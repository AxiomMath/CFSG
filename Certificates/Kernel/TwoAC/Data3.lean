module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
meta import CFSG.Certificates.Kernel.BabyMonster.TwinForest
public import Certificates.Kernel.TwoAC.Data2

#kc_eval CFSG.KC.BM.TwoAC S2 CFSG.KC.BM.Twin.forestSpin 4370 0 0 D.c0 V0 V1 2 a w2
#kc_eval CFSG.KC.BM.TwoAC S2A CFSG.KC.BM.Twin.prod 4370 0 0 S2 a
#kc_eval CFSG.KC.BM.TwoAC S2B CFSG.KC.BM.Twin.prod 4370 0 0 S2 w2
#kc_eval CFSG.KC.BM.TwoAC S3 CFSG.KC.BM.Twin.forestSpin 4370 0 0 D.c0 V0 V1 3 a w2
#kc_eval CFSG.KC.BM.TwoAC S3A CFSG.KC.BM.Twin.prod 4370 0 0 S3 a
#kc_eval CFSG.KC.BM.TwoAC S3B CFSG.KC.BM.Twin.prod 4370 0 0 S3 w2
#kc_eval CFSG.KC.BM.TwoAC P2 CFSG.KC.BM.Twin.rank 4370 0 0 S2 0 1
#kc_eval CFSG.KC.BM.TwoAC Q2 CFSG.KC.BM.Twin.polyMul 4370 0 0 P2 S2 0 1
#kc_eval CFSG.KC.BM.TwoAC P3 CFSG.KC.BM.Twin.rank 4370 0 0 S3 0 1
#kc_eval CFSG.KC.BM.TwoAC Q3 CFSG.KC.BM.Twin.polyMul 4370 0 0 P3 S3 0 1
