module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
meta import CFSG.Certificates.Kernel.BabyMonster.TwinForest
public import Certificates.Kernel.TwoAC.Data0

#kc_eval CFSG.KC.BM.TwoAC abb CFSG.KC.BM.Twin.prod 4370 0 0 ab w2
#kc_eval CFSG.KC.BM.TwoAC ba CFSG.KC.BM.Twin.prod 4370 0 0 w2 a
#kc_eval CFSG.KC.BM.TwoAC b3 CFSG.KC.BM.Twin.prod 4370 0 0 w4 w2
#kc_eval CFSG.KC.BM.TwoAC th0 CFSG.KC.BM.Twin.xorI 4370 0 0 0 ba abb a
#kc_eval CFSG.KC.BM.TwoAC th1 CFSG.KC.BM.Twin.xorI 4370 0 0 1 w2 abb b3
#kc_eval CFSG.KC.BM.TwoAC X1 CFSG.KC.BM.Twin.xorI 4370 0 0 1 x
#kc_eval CFSG.KC.BM.TwoAC Pt0 CFSG.KC.BM.Twin.rank 4370 0 0 th0 0 1
#kc_eval CFSG.KC.BM.TwoAC Qt0 CFSG.KC.BM.Twin.polyMul 4370 0 0 Pt0 th0 0 1
#kc_eval CFSG.KC.BM.TwoAC Pt1 CFSG.KC.BM.Twin.rank 4370 0 0 th1 0 1
#kc_eval CFSG.KC.BM.TwoAC Qt1 CFSG.KC.BM.Twin.polyMul 4370 0 0 Pt1 th1 0 1
#kc_eval CFSG.KC.BM.TwoAC Px CFSG.KC.BM.Twin.rank 4370 0 0 X1 0 1
#kc_eval CFSG.KC.BM.TwoAC Qx CFSG.KC.BM.Twin.polyMul 4370 0 0 Px X1 0 1
