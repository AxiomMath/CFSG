module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import Certificates.Kernel.TwoAC.Data0

#bm_mul4 CFSG.KC.BM.TwoAC cB2 CFSG.KC.BM.Seeds.A2 [CFSG.KC.BM.Seeds.A2] B2 []
#bm_mul4 CFSG.KC.BM.TwoAC cp CFSG.KC.BM.Seeds.A1 [B2] p []
#bm_mul4 CFSG.KC.BM.TwoAC cq CFSG.KC.BM.Seeds.A1 [CFSG.KC.BM.Seeds.A2] q []
#bm_mul4 CFSG.KC.BM.TwoAC cpq p [q] pq []
#bm_mul4 CFSG.KC.BM.TwoAC cs pq [p] s []
#bm_mul4 CFSG.KC.BM.TwoAC css s [s] ss []
#bm_mul4 CFSG.KC.BM.TwoAC cw ss [p] w []
#bm_mul4 CFSG.KC.BM.TwoAC cw2 w [w] w2 []
#bm_mul4 CFSG.KC.BM.TwoAC cw4 w2 [w2] w4 []
#bm_mul4 CFSG.KC.BM.TwoAC cw8 w4 [w4] w8 []
#bm_mul4 CFSG.KC.BM.TwoAC cw16 w8 [w8] w16 []
#bm_mul4 CFSG.KC.BM.TwoAC cx w16 [w] x []
#bm_mul4 CFSG.KC.BM.TwoAC cxx x [x] I []
