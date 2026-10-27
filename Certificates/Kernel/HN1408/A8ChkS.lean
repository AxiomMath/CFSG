module

public import Certificates.Kernel.HN1408.A8Data
public import Certificates.Data.Kernel.Spor.MulHF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def a8PeS (s : Nat) : Bool :=
  penumSlK 1408 11 (mask 11) (1408 * 11) true A8S.G A8S.GI 5 A8S.cnt A8S.T A8S.PL A8S.POS A8S.SRT
    A8S.SRI (Nat.mul 256 s) 256

@[expose] noncomputable def a8HsS : Bool :=
  slK A8S.cnt (hsortPtKF 1408 11 (mask 11) A8S.cnt A8S.T A8S.HS A8S.HSI) 0 A8S.cnt

theorem a8kPeS0 : a8PeS 0 = true := by quickRfl
theorem a8kPeS1 : a8PeS 1 = true := by quickRfl
theorem a8kPeS2 : a8PeS 2 = true := by quickRfl
theorem a8kHsS : a8HsS = true := by quickRfl

end CFSG.KD.HN1408

end
