module

public import Certificates.Data.Kernel.S8F28T
public import Certificates.Kernel.S8F28.Checks
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open CFSG.KC.S8F28K CFSG.KD.S8F28

#kc_each CFSG.KD.S8F28 ch7218_tcm (fun _ => tabCM CM MT) 0 1

#kc_each CFSG.KD.S8F28 ch7218_tfix (fun _ => CFSG.KC.Enum.allN 44 fun a => tabFix FMK a) 0 1

#kc_each CFSG.KD.S8F28 ch7218_tvec (fun _ => tabVec) 0 1

#kc_each CFSG.KD.S8F28 ch7218_k0 (fun _ => k0B) 0 1

#kc_each CFSG.KD.S8F28 ch7218_neg_c2 (fun _ => !c2K CM MT 0) 0 1

#kc_each CFSG.KD.S8F28 ch7218_neg_mt (fun _ => !tabCM CM (MT + 1)) 0 1
