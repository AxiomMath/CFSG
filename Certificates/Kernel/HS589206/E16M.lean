module

public import Certificates.Kernel.HS589206.E16D
public import Certificates.Data.Kernel.DcHSOutK
public import Certificates.Data.Kernel.DcK

public section

namespace CFSG.KD.HS589206.E16

open CFSG.KC.DcHSOutK

@[expose] noncomputable def ES : CFSG.KC.DcK.EnumK := CFSG.KC.DcK.recK 512 100 SR.TF

@[expose] noncomputable def ES5 : CFSG.KC.DcK.EnumK := CFSG.KC.DcK.recK 125 100 S5R.TF

@[expose] noncomputable def GS (t q : Nat) : Nat := fl (TS.TF t) q

@[expose] noncomputable def GS5 (t q : Nat) : Nat := fl (TS.TF (3 + t)) q

@[expose] noncomputable def sF (k q : Nat) : Nat := fl (SR.TF k) q

@[expose] noncomputable def ix (i : Nat) : Nat := fl (TS.TF 6) i

@[expose] noncomputable def IF (i q : Nat) : Nat := sF (ix i) q

@[expose] noncomputable def PT (a : Nat) : Nat := PR.TF a

@[expose] noncomputable def MK (t : Nat) : Nat := MR.TF t

end CFSG.KD.HS589206.E16

end
