module

public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Data.Kernel.Fi23R.Defs

@[expose] public section

namespace CFSG.KD.Fi23Cov

noncomputable def E : List Nat → List Nat → Bool := CFSG.KC.Fi23R.eqB CFSG.KD.Fi23K.G

end CFSG.KD.Fi23Cov

end
