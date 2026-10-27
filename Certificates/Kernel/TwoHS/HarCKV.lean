module

public import Certificates.Kernel.TwoHS.HarCDV
public import Certificates.Data.Kernel.Spor.HKeyU
public import Certificates.Data.Kernel.Spor.PEnumB
public import Certificates.Kernel.TwoHS.HarCD

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.KS.PEnumB

@[expose] noncomputable def ch7291jHv (i : Nat) : Bool :=
  Nat.beq (hkeyU 11200 14 (mask 14) (TE.T i)) (TEV i)

@[expose] noncomputable def ch7291hv (k : Nat) : Bool := slK TE.cnt ch7291jHv (Nat.mul 64 k) 64

@[expose] noncomputable def ch7291hsv : Bool :=
  slK TE.cnt (hsortVK TE.cnt TEV TE.HS TE.HSI) 0 1024

end CFSG.KD.TwoHS

end
