module

public import Certificates.Kernel.LocalQT.Pairs.C4094h
import Certificates.Kernel.Sporadic.ON.Gen

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4094

open CFSG.KC.LQT.PH CFSG.KC.LQT.L CFSG.KD.LQT.M24Chain

@[expose] noncomputable def k2f (j : Nat) : Bool := chainChunk 24 CK2 fK2 j

@[expose] noncomputable def k2h (r : Nat) : Bool := hkR 24 CK2 3 r

end CFSG.KD.LQT.C4094

#kon_slices CFSG.KD.LQT.C4094.k2f 0 24
#kon_slices CFSG.KD.LQT.C4094.k2h 0 3

end
