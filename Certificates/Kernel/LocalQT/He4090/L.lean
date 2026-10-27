module

public import Certificates.Kernel.LocalQT.Base.C4141D
public import Certificates.Kernel.LocalQT.He4090.D
public import Certificates.Data.Kernel.LocalQT.PcW
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHeWitInputs

public section

namespace CFSG.KD.LQT.H4090

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] noncomputable def Lab (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), CFSG.KD.LQT.C4141.TF (nat_lit 0), CFSG.KD.LQT.C4141.TF (nat_lit 1))

@[expose] noncomputable def L2c (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), CFSG.KD.LQT.C4141.TF (nat_lit 197),
  nIf(Nat.beq l (nat_lit 1), CFSG.KD.LQT.C4141.TF (nat_lit 207),
  nIf(Nat.beq l (nat_lit 2), CFSG.KD.LQT.C4141.TF (nat_lit 226),
  nIf(Nat.beq l (nat_lit 3), CFSG.KD.LQT.C4141.TF (nat_lit 247), TF (nat_lit 1)))))

@[expose] noncomputable def L7c (l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), CFSG.KD.LQT.C4141.TF (nat_lit 197),
  nIf(Nat.beq l (nat_lit 1), CFSG.KD.LQT.C4141.TF (nat_lit 207),
  nIf(Nat.beq l (nat_lit 2), CFSG.KD.LQT.C4141.TF (nat_lit 226),
  nIf(Nat.beq l (nat_lit 3), CFSG.KD.LQT.C4141.TF (nat_lit 247), TF (nat_lit 3)))))

@[expose] noncomputable def nthQ (l : List QuotGen) (i : Nat) : QuotGen :=
  List.rec (motive := fun _ => Nat → QuotGen) (fun _ => default)
    (fun x _ ih j => Bool.rec (motive := fun _ => QuotGen) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i

end CFSG.KD.LQT.H4090

end
