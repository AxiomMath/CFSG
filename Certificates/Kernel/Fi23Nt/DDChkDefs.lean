module

public import Certificates.Data.Kernel.Fi23Nt.DDDefs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23Nt.DataDD

public section

namespace CFSG.KD.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23Nt CFSG.KD.Fi23K

@[expose] noncomputable def ddSlOf (W : List (List Nat)) (s : Nat) : Bool :=
  ddSlK G W (Nat.mul s (nat_lit 1024)) (nIf(Nat.beq s (nat_lit 30), nat_lit 951, nat_lit 1024))

@[expose] noncomputable def ddSl (s : Nat) : Bool := ddSlOf ddW s

end CFSG.KD.Fi23Nt

end
