module

public import Certificates.Data.Kernel.Fi23Cls.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23Cls.Data

public section

namespace CFSG.KD.Fi23Cls

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23Five CFSG.KC.Fi23Cls CFSG.KD.Fi23K

@[expose] def w0 : List Nat := [2, 3]
@[expose] def w1 : List Nat :=
  [71, 59, 55, 52, 65, 71, 59, 56, 67, 60, 66, 61, 74, 70, 65, 72, 70, 68, 68]
@[expose] def w2 : List Nat := [4, 5, 2, 1]
@[expose] def w3 : List Nat := [5, 3, 7, 0, 6, 1]

@[expose] noncomputable def scan0 : Bool := fixK G w0 L0
@[expose] noncomputable def scan1 : Bool := fixK G w1 L1
@[expose] noncomputable def scan2 : Bool := fixK G w2 L2
@[expose] noncomputable def scan3 : Bool := fixK G w3 L3

@[expose] noncomputable def cls0 : Bool := clsK G w0 (nat_lit 106) (nat_lit 351) (nat_lit 126) L0 S0
@[expose] noncomputable def cls1 : Bool := clsK G w1 (nat_lit 216) (nat_lit 324) (nat_lit 27) L1 S1
@[expose] noncomputable def cls2 : Bool := clsK G w2 (nat_lit 544) (nat_lit 135) (nat_lit 36) L2 S2
@[expose] noncomputable def cls3 : Bool := clsK G w3 (nat_lit 8) (nat_lit 27) (nat_lit 0) L3 S3

end CFSG.KD.Fi23Cls

end
