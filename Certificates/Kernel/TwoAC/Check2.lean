module

import CFSG.Certificates.Kernel.BabyMonster.LoadFour
import CFSG.Certificates.Kernel.BabyMonster.Load
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.SoundDefs
public import Certificates.Data.Kernel.TwoAC.Check
public import Certificates.Kernel.TwoAC.Data0
public import Certificates.Kernel.TwoAC.Data1
public import CFSG.Certificates.Kernel.BSeed.Sound

#bm_mul4 CFSG.KC.BM.TwoAC cabb ab [w2] abb []
#bm_mul4 CFSG.KC.BM.TwoAC cba w2 [a] ba []
#bm_mul4 CFSG.KC.BM.TwoAC cb3 w4 [w2] b3 []
#bm_range CFSG.KC.BM.TwoAC xth0_ 0 69 (CFSG.KC.BM.TwoAC.xorRowL th0 (L2 ba abb a))
#bm_range CFSG.KC.BM.TwoAC xth1_ 0 69 (CFSG.KC.BM.TwoAC.xorRowL th1 (L2 w2 abb b3 CFSG.KC.BM.idStrips))
#bm_range CFSG.KC.BM.TwoAC xX1_ 0 69 (CFSG.KC.BM.TwoAC.xorRowL X1 (L2 x CFSG.KC.BM.idStrips))
#bm_mul4 CFSG.KC.BM.TwoAC cPt0 Pt0 [th0] Qt0 []
#bm_mul4 CFSG.KC.BM.TwoAC cPt1 Pt1 [th1] Qt1 []
#bm_mul4 CFSG.KC.BM.TwoAC cPx Px [X1] Qx []
#bm_bool CFSG.KC.BM.TwoAC shape_t0 (CFSG.KC.BM.shapeOK Qt0 4367)
#bm_bool CFSG.KC.BM.TwoAC shape_t1 (CFSG.KC.BM.shapeOK Qt1 4366)
#bm_bool CFSG.KC.BM.TwoAC shape_x (CFSG.KC.BM.shapeOK Qx 1860)
#bm_bool CFSG.KC.BM.TwoAC ech_x (CFSG.KC.BM.echFrom Px 1860)
