module

public import Certificates.Kernel.LocalQT.TabA2.D4043
public import Certificates.Kernel.LocalQT.Tc.Gen

public section

namespace CFSG.KD.LQT.TA

open CFSG.KS.TabA2

@[expose] noncomputable def ckS (s : Nat) : Bool :=
  sK S.G S.T S.PL S.POS S.SRT S.SRI U V (X (nat_lit 2)) S.cnt (Nat.mul s (nat_lit 64)) (nat_lit 64)

end CFSG.KD.LQT.TA

end
