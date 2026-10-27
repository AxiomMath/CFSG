module

public import Certificates.Kernel.HN1408.M11HV
public import Certificates.Data.Kernel.Spor.PEnumR
public import Certificates.Data.Kernel.Spor.PEnumB

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumR CFSG.KS.PEnumB

@[expose] noncomputable def peR (s : Nat) : Bool :=
  slK MR1.cnt (penumPtR 1408 11 (mask 11) MR1.GI 2 MR1.cnt MR1.T MR1.PL MR1.POS MR1.SRT MR1.SRI)
    (Nat.mul 990 s) 990

@[expose] noncomputable def hvR (s : Nat) : Bool :=
  slK MR1.cnt (hvF 1408 11 (mask 11) MR1.T MR1V) (Nat.mul 495 s) 495

@[expose] noncomputable def hsR (s : Nat) : Bool :=
  slK MR1.cnt (hsortVK MR1.cnt MR1V MR1.HS MR1.HSI) (Nat.mul 3960 s) 3960

end CFSG.KD.HN1408

end
