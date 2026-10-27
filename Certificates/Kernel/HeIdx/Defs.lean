module

public import Certificates.Kernel.HeDc.Defs

public noncomputable section

namespace CFSG.KD.HeIdx

@[expose] def Sl (l : Nat) : Nat → Nat := CFSG.KD.HeDc.L (Nat.add 2 l)

@[expose] def Z (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF 170) p

@[expose] def mlen (j : Nat) : Nat := (CFSG.KD.HeDc.J.mw.getD j []).length

end CFSG.KD.HeIdx

end
