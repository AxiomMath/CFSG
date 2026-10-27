module

public import Certificates.Kernel.RuIdx2.Defs
public import Certificates.Data.Kernel.RuIdx2VK

public section

namespace CFSG.KD.RuIdx2

open CFSG.KC.RuIdx2 CFSG.KC.Enum

@[expose] noncomputable def famV (u : Nat) : Bool := allN (nR u) fun i => wltK (RW u i)

end CFSG.KD.RuIdx2

end
