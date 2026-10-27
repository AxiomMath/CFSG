module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import Certificates.Kernel.TwoAC.Data0

#bm_mul4 CFSG.KC.BM.TwoAC cq2 q [q] q2 []
#bm_mul4 CFSG.KC.BM.TwoAC cg B2 [q2] g []
#bm_mul4 CFSG.KC.BM.TwoAC cB2p B2 [p] B2p []
#bm_mul4 CFSG.KC.BM.TwoAC cgi B2p [q] gi []
#bm_mul4 CFSG.KC.BM.TwoAC cggi g [gi] I []
#bm_mul4 CFSG.KC.BM.TwoAC cxgi x [gi] xgi []
#bm_mul4 CFSG.KC.BM.TwoAC cxgix xgi [x] xgix []
#bm_mul4 CFSG.KC.BM.TwoAC cr28 xgix [g] r28 []
#bm_mul4 CFSG.KC.BM.TwoAC ca r28 [r28] a []
#bm_mul4 CFSG.KC.BM.TwoAC caa a [a] I []
#bm_mul4 CFSG.KC.BM.TwoAC cab a [w2] ab []
#bm_mul4 CFSG.KC.BM.TwoAC cab2 ab [ab] ab2 []
#bm_mul4 CFSG.KC.BM.TwoAC cab4 ab2 [ab2] ab4 []
#bm_mul4 CFSG.KC.BM.TwoAC cab8 ab4 [ab4] ab8 []
#bm_mul4 CFSG.KC.BM.TwoAC cab12 ab8 [ab4] ab12 []
#bm_mul4 CFSG.KC.BM.TwoAC cab13 ab12 [ab] I []
