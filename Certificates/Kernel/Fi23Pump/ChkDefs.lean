module

public import Certificates.Data.Kernel.Fi23Pump.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23Pump.Data

public section

namespace CFSG.KD.Fi23Pump

open CFSG.KC.Fi23Pump CFSG.KD.Fi23K

@[expose] def y1R : List Nat := [64, 67, 55, 52, 60, 60, 58, 56, 71, 64, 71, 68, 60, 68, 65, 68, 64,
  74, 70, 69, 70, 74]

@[expose] def y2R : List Nat := [54, 74, 56, 55, 52, 61, 72, 69, 56, 64, 62, 64, 63, 67, 68, 65, 71,
  69, 74, 71, 69, 72]

@[expose] def t2R : List Nat := [4, 5, 2, 1]

@[expose] noncomputable def y1K : Bool := yK G y1R t2R
@[expose] noncomputable def y2K : Bool := yK G y2R t2R

@[expose] noncomputable def orbOK : Bool := orbK G y1R y2R P (nat_lit 1081) (nat_lit 1)

end CFSG.KD.Fi23Pump

end
