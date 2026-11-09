module

public import Certificates.Kernel.TwoHS.HarCK
public import Certificates.Kernel.TwoHS.HarCN
public import Certificates.Data.Kernel.Spor.MulHPc

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def ntE (r k : Nat) : Bool :=
  slK (Nat.shiftLeft 1 r) (pcTK 11200 14 (mask 14) TE.T TEP r) (Nat.mul 16 k) 16

@[expose] noncomputable def ntE5 (k : Nat) : Bool := ntE 5 k

@[expose] noncomputable def ntE6 (k : Nat) : Bool := ntE 6 k

@[expose] noncomputable def ntE7 (k : Nat) : Bool := ntE 7 k

@[expose] noncomputable def ntE8 (k : Nat) : Bool := ntE 8 k

@[expose] noncomputable def ntE9 (k : Nat) : Bool := ntE 9 k

@[expose] noncomputable def ntQ (r k : Nat) : Bool :=
  slK (Nat.shiftLeft 1 r) (pcTK 11200 14 (mask 14) TQ.T TQP r) (Nat.mul 16 k) 16

@[expose] noncomputable def ntQ5 (k : Nat) : Bool := ntQ 5 k

@[expose] noncomputable def ntQ6 (k : Nat) : Bool := ntQ 6 k

@[expose] noncomputable def rlE (r c : Nat) : Bool :=
  pcRK 11200 14 (mask 14) 10 TE.T TEP TEA TEB r (Nat.mul 4 c) 4

@[expose] noncomputable def rlQ (r c : Nat) : Bool :=
  pcRK 11200 14 (mask 14) 7 TQ.T TQP TQA TQB r (Nat.mul 4 c) 4

@[expose] noncomputable def mbE : Bool :=
  pcMK 11200 14 (mask 14) 3 TE.cnt 5 TE.T TE.GI TEP TES TEU TEPP

@[expose] noncomputable def mbQ : Bool :=
  pcMK 11200 14 (mask 14) 6 TQ.cnt 2 TQ.T TQ.GI TQP TQS TQU TQPP

@[expose] noncomputable def clPE (k : Nat) : Bool :=
  slK (Nat.mul TE.cnt 6) (pcCK 14 (mask 14) 3 TE.cnt 5 TE.T TE.GI TECl) (Nat.mul 1024 k) 1024

@[expose] noncomputable def clPQ (k : Nat) : Bool :=
  slK (Nat.mul TQ.cnt 12) (pcCK 14 (mask 14) 6 TQ.cnt 2 TQ.T TQ.GI TQCl) (Nat.mul 768 k) 768

end CFSG.KD.TwoHS

end
