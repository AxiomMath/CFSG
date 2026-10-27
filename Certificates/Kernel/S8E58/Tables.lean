module

public import Certificates.Data.Kernel.S8E58T
public import Certificates.Kernel.S8E58.Checks
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open CFSG.KC.S8E58K CFSG.KD.S8E58

#kc_each CFSG.KD.S8E58 ch7158_tcm (fun _ => tabCM CM MT) 0 1

#kc_each CFSG.KD.S8E58 ch7158_tfx (fun _ => tabFX FX) 0 1

#kc_each CFSG.KD.S8E58 ch7158_k0 (fun _ => k0B) 0 1

#kc_each CFSG.KD.S8E58 ch7158_neg_k34
  (fun _ => !k34K CM MT (Nat.sub (Nat.shiftLeft 1 352) 1) R W 0) 0 1

#kc_each CFSG.KD.S8E58 ch7158_neg_fx (fun _ => !tabFX (FX + 1)) 0 1

#kc_each CFSG.KD.S8E58 ch7158_neg_mt (fun _ => !tabCM CM (MT + 1)) 0 1
