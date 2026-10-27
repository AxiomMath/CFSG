module

public import Certificates.Kernel.LocalQT.HSAut.D4146
public import Certificates.Kernel.LocalQT.Tc.Gen

public section

namespace CFSG.KD.LQT.HN

open CFSG.KS.HSAutN

@[expose] noncomputable def ckA (s : Nat) : Bool :=
  nSlK A.G A.G A.T A.PL A.POS A.SRT A.SRI (X (nat_lit 0)) (X (nat_lit 1)) (X (nat_lit 2))
    (X (nat_lit 3)) (X (nat_lit 4)) A.cnt (Nat.mul s (nat_lit 8)) (nat_lit 8)

end CFSG.KD.LQT.HN

end
