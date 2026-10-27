module

public import Certificates.Kernel.TwoHS.HarCK
public import Certificates.Data.Kernel.Spor.MulHF
import CFSG.Certificates.Kernel.Common.Each

set_option maxRecDepth 400000

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def ch7291hsF (k : Nat) : Bool :=
  slK TQ.cnt (hsortPtKF 11200 14 (mask 14) TQ.cnt TQ.T TQ.HS TQ.HSI) (Nat.mul 64 k) 64

theorem ch7291hsF_neg :
    hsortPtKF 11200 14 (mask 14) TQ.cnt (fun _ => 0) TQ.HS TQ.HSI 0 = false := by
  decide +kernel

end CFSG.KD.TwoHS

end

#kc_each CFSG.KD.TwoHS.peQ 0 8
#kc_each CFSG.KD.TwoHS.ch7291hsF 0 2
#kc_each CFSG.KD.TwoHS.clQ 0 12
#kc_each CFSG.KD.TwoHS.nqQ 0 10
