module

public import Certificates.Kernel.Misc.Coset.XSz8HA.Data
public import Certificates.Data.Sz8CoverInvolutions

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.XSz8H.Inv7262

open CFSG.LieType.Multipliers.Sz8 CFSG.Certificates.CosetEnumeration CFSG.KC.MiscCoset

theorem invCyc : (invWords.all fun p =>
    Act.cycleOK CFSG.KAct.XSz8H.A (Nat.add 2 2) (p.1.map letterCode) p.2) = true := by
  decide +kernel

end CFSG.KAct.XSz8H.Inv7262

end
