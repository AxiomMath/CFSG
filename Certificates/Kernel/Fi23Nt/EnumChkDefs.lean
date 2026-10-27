module

public import Certificates.Data.Kernel.Fi23Nt.EnumDefs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23Nt.DataE

public section

namespace CFSG.KD.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23Nt CFSG.KD.Fi23K

@[expose] noncomputable def enumBSlOf (W : List (List Nat)) (s : Nat) : Bool :=
  enumSlK G W (nat_lit 3) eBN eBPar eBImg eBLt (Nat.mul s (nat_lit 81)) (nat_lit 81)

@[expose] noncomputable def enumBSl (s : Nat) : Bool := enumBSlOf eBW s

@[expose] noncomputable def enumCSl (s : Nat) : Bool :=
  enumSlK G eCW (nat_lit 3) eCN eCPar eCImg eCLt (Nat.mul s (nat_lit 81)) (nat_lit 81)

@[expose] noncomputable def ordB : Bool := ordK eBImg eBOrd eBN

@[expose] noncomputable def ordC : Bool := ordK eCImg eCOrd eCN

end CFSG.KD.Fi23Nt

end
