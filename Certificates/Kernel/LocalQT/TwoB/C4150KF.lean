module

public import Certificates.Data.Kernel.Spor.MulHF
public import Certificates.Kernel.LocalQT.TwoB.C4150D

public section

namespace CFSG.KD.LQT.TB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def ckHF (s : Nat) : Bool :=
  slK Y.cnt (hsortPtKF 3850 12 (mask 12) Y.cnt Y.T Y.HS Y.HSI) (Nat.mul s 8) 8

end CFSG.KD.LQT.TB

end
