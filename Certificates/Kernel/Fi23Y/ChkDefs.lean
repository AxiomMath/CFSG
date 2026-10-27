module

public import Certificates.Data.Kernel.Fi23Y.Defs
public import Certificates.Kernel.Fi23S.ChkDefs
public import Certificates.Kernel.Fi23Y.Data

public section

namespace CFSG.KD.Fi23Y

open CFSG.KC.Enum CFSG.KC.Fi23Y CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23S CFSG.KS.PEnum

@[expose] noncomputable def GL (l x : Nat) : Nat :=
  gK (Nat.shiftRight l (nat_lit 9)) (Nat.land l (nat_lit 511)) x

@[expose] noncomputable def TR (k x : Nat) : Nat := tA G k x

@[expose] noncomputable def CD (l : Nat) : Nat := r32 CW l

@[expose] noncomputable def FJ (l : Nat) : Nat := r32 CJ l
@[expose] noncomputable def FW (f : Nat) : Nat := r32 WT f

@[expose] noncomputable def rootsF : Bool :=
  bAnd(allN (nat_lit 3) (rootY GL CD LS FW), allN (nat_lit 96) (repY CD FW))

@[expose] noncomputable def cenF (s : Nat) : Bool :=
  allN (nat_lit 32768) fun d =>
    strictB (Nat.add (Nat.mul s (nat_lit 32768)) d) (cenY GL CD FJ FW)

@[expose] noncomputable def entF (i : Nat) : Bool := allN (nat_lit 96) (entY GL TR CD FW i)

end CFSG.KD.Fi23Y

end
