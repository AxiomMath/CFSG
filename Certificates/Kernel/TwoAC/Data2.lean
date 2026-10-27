module

import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Bounds.LoadRoot
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinVec
meta import CFSG.Certificates.Kernel.BabyMonster.TwinForest
public import Certificates.Kernel.TwoAC.Data0

#kc_repo #kc_list_root CFSG.KC.BM.TwoAC.D "Certificates/Kernel/TwoAC/data/twoac.items" 4370 33934 7787285997450021867
#kc_eval CFSG.KC.BM.TwoAC Fb CFSG.KC.BM.Twin.blocks D.c0 64
#kc_eval CFSG.KC.BM.TwoAC V0 CFSG.KC.BM.Twin.vecStrip 4370 0 0 D.c1 0 2
#kc_eval CFSG.KC.BM.TwoAC V1 CFSG.KC.BM.Twin.vecStrip 4370 0 0 D.c1 1 2
#kc_eval CFSG.KC.BM.TwoAC Bv CFSG.KC.BM.Twin.forestSpin 4370 0 0 D.c0 V0 V1 0 a w2
#kc_eval CFSG.KC.BM.TwoAC BvA CFSG.KC.BM.Twin.prod 4370 0 0 Bv a
#kc_eval CFSG.KC.BM.TwoAC BvB CFSG.KC.BM.Twin.prod 4370 0 0 Bv w2
#kc_eval CFSG.KC.BM.TwoAC Binv CFSG.KC.BM.Twin.inv 4370 0 0 Bv
#kc_eval CFSG.KC.BM.TwoAC betaA CFSG.KC.BM.Twin.vword 4370 0 0 CFSG.KC.BM.Seeds.A1 Bv a Binv
#kc_eval CFSG.KC.BM.TwoAC betaB CFSG.KC.BM.Twin.vword 4370 0 0 CFSG.KC.BM.Seeds.A1 Bv w2 Binv
