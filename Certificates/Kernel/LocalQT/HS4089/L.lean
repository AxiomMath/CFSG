module

public import Certificates.Kernel.LocalQT.HS4089.SD
public import Certificates.Kernel.LocalQT.HS4089.D
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KD.LQT.H4089

@[expose] noncomputable def Lab (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), CFSG.KD.LQT.H4089S.TF (nat_lit 0), CFSG.KD.LQT.H4089S.TF (nat_lit 1))

@[expose] noncomputable def L1c (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), CFSG.KD.LQT.H4089S.TF (nat_lit 172),
  nIf(Nat.beq l (nat_lit 1), CFSG.KD.LQT.H4089S.TF (nat_lit 185),
  nIf(Nat.beq l (nat_lit 2), CFSG.KD.LQT.H4089S.TF (nat_lit 200), TF (nat_lit 1))))

@[expose] noncomputable def L2c (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), CFSG.KD.LQT.H4089S.TF (nat_lit 172),
  nIf(Nat.beq l (nat_lit 1), CFSG.KD.LQT.H4089S.TF (nat_lit 185),
  nIf(Nat.beq l (nat_lit 2), CFSG.KD.LQT.H4089S.TF (nat_lit 200), TF (nat_lit 2))))

end CFSG.KD.LQT.H4089

end
