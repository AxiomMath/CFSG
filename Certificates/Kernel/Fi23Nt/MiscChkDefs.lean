module

public import Certificates.Data.Kernel.Fi23Nt.EnumDefs
public import Certificates.Data.Kernel.Fi23Nt.MiscDefs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23Nt.Data
public import Certificates.Kernel.Fi23Nt.DataB
public import Certificates.Kernel.Fi23Nt.DataE
public import Certificates.Kernel.Fi23Nt.DataM

public section

namespace CFSG.KD.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23Nt CFSG.KD.Fi23K

@[expose] noncomputable def enumPSl (s : Nat) : Bool :=
  enumSlK G ePW (nat_lit 4) ePN ePPar ePImg ePLt (Nat.mul s (nat_lit 81)) (nat_lit 81)

@[expose] noncomputable def ordP : Bool := ordK ePImg ePOrd ePN

@[expose] noncomputable def cbB : Bool := cbK G ePW bW

@[expose] noncomputable def t2C : Bool := t2K G eCW

@[expose] noncomputable def hyC : Bool := hyK G hW v0 yW

@[expose] noncomputable def pairB : Bool := pairsK G fixF pX

end CFSG.KD.Fi23Nt

end
