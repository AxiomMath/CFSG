module

public import Certificates.Data.Kernel.Fi23Nt.Defs
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23K.Trees
public import Certificates.Kernel.Fi23Nt.Data

public section

namespace CFSG.KD.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23Nt CFSG.KD.Fi23K CFSG.KS.PEnum

@[expose] noncomputable def POS0 (v : Nat) : Nat := r32 (TT (nat_lit 0) (nat_lit 1)) v

@[expose] noncomputable def PAR0 (k : Nat) : Nat := r32 (TT (nat_lit 0) (nat_lit 2)) k

@[expose] noncomputable def LAB0 (k : Nat) : Nat := r32 (TT (nat_lit 0) (nat_lit 3)) k

@[expose] noncomputable def slLen (s : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 30), nat_lit 951, nat_lit 1024)

@[expose] noncomputable def filtSlOf (S : List (List Nat × Bool)) (s c : Nat) : Bool :=
  cntSlK POS0 PAR0 LAB0 G S (Nat.mul s (nat_lit 1024)) (slLen s) c

@[expose] noncomputable def filtSl (s : Nat) : Bool := filtSlOf st s (List.getD cnt s (nat_lit 0))

@[expose] noncomputable def cntSum : Bool :=
  Nat.beq (List.foldr Nat.add (nat_lit 0) cnt) (nat_lit 486)

end CFSG.KD.Fi23Nt

end
