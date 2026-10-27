module

public import Certificates.Kernel.LocalQT.TabA2.D4045
public import Certificates.Kernel.LocalQT.Tc.Gen

public section

namespace CFSG.KD.LQT.TL

open CFSG.KS.TabL34 CFSG.KD.LQT.TA

@[expose] noncomputable def ckR (s : Nat) : Bool :=
  rsK R.G R.T R.PL R.POS R.SRT R.SRI S.T CG (X (nat_lit 2)) kC R.cnt (Nat.mul s (nat_lit 64))
    (nat_lit 64)

@[expose] noncomputable def ckT (s : Nat) : Bool :=
  tsK S.T TW (X (nat_lit 2)) S.cnt (Nat.mul s (nat_lit 64)) (nat_lit 64)

end CFSG.KD.LQT.TL

end
