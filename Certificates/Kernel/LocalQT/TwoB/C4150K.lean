module

public import Certificates.Kernel.LocalQT.TwoB.C4150D
public import Certificates.Kernel.LocalQT.Tc.Gen

public section

namespace CFSG.KD.LQT.TB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def ckE (s : Nat) : Bool :=
  penumSlK 3850 12 (mask 12) (3850 * 12) true Y.G Y.GI 2 Y.cnt Y.T Y.PL Y.POS Y.SRT Y.SRI
    (Nat.mul s 4) 4

@[expose] noncomputable def ckH (s : Nat) : Bool :=
  slK Y.cnt (hsortPtK 3850 12 (mask 12) Y.cnt Y.T Y.HS Y.HSI) (Nat.mul s 8) 8

@[expose] noncomputable def ckC (s : Nat) : Bool :=
  slK (Nat.mul Y.cnt 4) (findPtK Y.cnt Y.T (prodQK 3850 12 (mask 12) 4 Y.T (bothK 2 Y.GI YI)) YCl)
    (Nat.mul s 8) 8

@[expose] noncomputable def ckN (s : Nat) : Bool :=
  slK (Nat.mul Y.cnt 4) (findPtK Y.cnt Y.T (conjQK 3850 12 (mask 12) 4 Y.T cC cCI) YNm)
    (Nat.mul s 4) 4

@[expose] noncomputable def ckM (s : Nat) : Bool :=
  slK 16 (findPtK Y.cnt Y.T (commQK 3850 12 (mask 12) 4 cC cCI) YCm) (Nat.mul s 2) 2

end CFSG.KD.LQT.TB

end
