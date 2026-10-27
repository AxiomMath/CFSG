module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0

#kc_eval CFSG.KC.BM.TwoAC B2 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A2 CFSG.KC.BM.Seeds.A2
#kc_eval CFSG.KC.BM.TwoAC p CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A1 B2
#kc_eval CFSG.KC.BM.TwoAC q CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Seeds.A1 CFSG.KC.BM.Seeds.A2
#kc_eval CFSG.KC.BM.TwoAC pq CFSG.KC.BM.Twin.prod 4370 0 0 p q
#kc_eval CFSG.KC.BM.TwoAC s CFSG.KC.BM.Twin.prod 4370 0 0 pq p
#kc_eval CFSG.KC.BM.TwoAC ss CFSG.KC.BM.Twin.prod 4370 0 0 s s
#kc_eval CFSG.KC.BM.TwoAC w CFSG.KC.BM.Twin.prod 4370 0 0 ss p
#kc_eval CFSG.KC.BM.TwoAC w2 CFSG.KC.BM.Twin.prod 4370 0 0 w w
#kc_eval CFSG.KC.BM.TwoAC w4 CFSG.KC.BM.Twin.prod 4370 0 0 w2 w2
#kc_eval CFSG.KC.BM.TwoAC w8 CFSG.KC.BM.Twin.prod 4370 0 0 w4 w4
#kc_eval CFSG.KC.BM.TwoAC w16 CFSG.KC.BM.Twin.prod 4370 0 0 w8 w8
#kc_eval CFSG.KC.BM.TwoAC x CFSG.KC.BM.Twin.prod 4370 0 0 w16 w
#kc_eval CFSG.KC.BM.TwoAC q2 CFSG.KC.BM.Twin.prod 4370 0 0 q q
#kc_eval CFSG.KC.BM.TwoAC g CFSG.KC.BM.Twin.prod 4370 0 0 B2 q2
#kc_eval CFSG.KC.BM.TwoAC B2p CFSG.KC.BM.Twin.prod 4370 0 0 B2 p
#kc_eval CFSG.KC.BM.TwoAC gi CFSG.KC.BM.Twin.prod 4370 0 0 B2p q
#kc_eval CFSG.KC.BM.TwoAC xgi CFSG.KC.BM.Twin.prod 4370 0 0 x gi
#kc_eval CFSG.KC.BM.TwoAC xgix CFSG.KC.BM.Twin.prod 4370 0 0 xgi x
#kc_eval CFSG.KC.BM.TwoAC r28 CFSG.KC.BM.Twin.prod 4370 0 0 xgix g
#kc_eval CFSG.KC.BM.TwoAC a CFSG.KC.BM.Twin.prod 4370 0 0 r28 r28
#kc_eval CFSG.KC.BM.TwoAC ab CFSG.KC.BM.Twin.prod 4370 0 0 a w2
#kc_eval CFSG.KC.BM.TwoAC ab2 CFSG.KC.BM.Twin.prod 4370 0 0 ab ab
#kc_eval CFSG.KC.BM.TwoAC ab4 CFSG.KC.BM.Twin.prod 4370 0 0 ab2 ab2
#kc_eval CFSG.KC.BM.TwoAC ab8 CFSG.KC.BM.Twin.prod 4370 0 0 ab4 ab4
#kc_eval CFSG.KC.BM.TwoAC ab12 CFSG.KC.BM.Twin.prod 4370 0 0 ab8 ab4
