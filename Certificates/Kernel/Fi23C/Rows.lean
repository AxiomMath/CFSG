module

public import Certificates.Data.Kernel.Fi23C.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23C.Data
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23C

open CFSG.KC.Fi23C CFSG.KD.Fi23K

@[expose] noncomputable def rs (s : Nat) : Bool := rowSl G H (nat_lit 2) s

end CFSG.KD.Fi23C

#kon_slices CFSG.KD.Fi23C.rs 0 7

end
