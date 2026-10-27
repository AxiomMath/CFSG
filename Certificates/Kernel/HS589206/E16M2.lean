module

public import Certificates.Kernel.HS589206.E16D2
public import Certificates.Data.Kernel.DcHSOutK
public import Certificates.Kernel.HS589206.E16D

public section

namespace CFSG.KD.HS589206.E16

open CFSG.KC.DcHSOutK

@[expose] noncomputable def eR (t s : Nat) : Nat := fl (ER.TF t) s

@[expose] noncomputable def s5F (k q : Nat) : Nat := fl (S5R.TF k) q

end CFSG.KD.HS589206.E16

end
