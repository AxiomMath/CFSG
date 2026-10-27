module

public import Certificates.Kernel.LocalQT.Pairs.C4094h
import Certificates.Kernel.Sporadic.ON.Gen

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4094

open CFSG.KC.LQT.PH CFSG.KD.LQT.M24Chain

@[expose] noncomputable def k1h (r : Nat) : Bool := hkR 24 CK1 6 r

end CFSG.KD.LQT.C4094

#kon_slices CFSG.KD.LQT.C4094.k1h 0 6

end
