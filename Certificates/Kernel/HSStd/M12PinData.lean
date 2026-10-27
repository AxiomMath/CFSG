module

public import Certificates.Kernel.HSStd.M12PinGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Lie.CT.Core
meta import Certificates.Kernel.HSStd.M12PinGen

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelHSStd.M12.TP CertificateChecks.KernelHSStd.M12PinGen.mT 72
#kmisc_packarrs CertificateChecks.KernelHSStd.M12.EP CertificateChecks.KernelHSStd.M12PinGen.mE 34
#kmisc_packarrs CertificateChecks.KernelHSStd.M12.SP CertificateChecks.KernelHSStd.M12PinGen.mS 17
#kmisc_packarrs CertificateChecks.KernelHSStd.M12.SIP CertificateChecks.KernelHSStd.M12PinGen.mSI 17
#kmisc_packarrs CertificateChecks.KernelHSStd.M12.C CertificateChecks.KernelHSStd.M12PinGen.mC 32
#kmisc_packarrs CertificateChecks.KernelHSStd.M12.G CertificateChecks.KernelHSStd.M12PinGen.gP 72
#kmisc_packarrs CertificateChecks.KernelHSStd.M12.GI CertificateChecks.KernelHSStd.M12PinGen.giP 72
#kmisc_packarrs CertificateChecks.KernelHSStd.M12A.TP CertificateChecks.KernelHSStd.M12PinGen.aT 72
#kmisc_packarrs CertificateChecks.KernelHSStd.M12A.EP CertificateChecks.KernelHSStd.M12PinGen.aE 20
#kmisc_packarrs CertificateChecks.KernelHSStd.M12A.SP CertificateChecks.KernelHSStd.M12PinGen.aS 10
#kmisc_packarrs CertificateChecks.KernelHSStd.M12A.SIP CertificateChecks.KernelHSStd.M12PinGen.aSI 10
#kmisc_packarrs CertificateChecks.KernelHSStd.M12B.TP CertificateChecks.KernelHSStd.M12PinGen.bT 72
#kmisc_packarrs CertificateChecks.KernelHSStd.M12B.EP CertificateChecks.KernelHSStd.M12PinGen.bE 20
#kmisc_packarrs CertificateChecks.KernelHSStd.M12B.SP CertificateChecks.KernelHSStd.M12PinGen.bS 10
#kmisc_packarrs CertificateChecks.KernelHSStd.M12B.SIP CertificateChecks.KernelHSStd.M12PinGen.bSI 10
#kmisc_packarrs CertificateChecks.KernelHSStd.M12.W CertificateChecks.KernelHSStd.M12PinGen.coverW 11
#kmisc_packarrs CertificateChecks.KernelHSStd.M12.AB CertificateChecks.KernelHSStd.M12PinGen.abX 32
#kmisc_packarrs CertificateChecks.KernelHSStd.M12C.X CertificateChecks.KernelHSStd.M12PinGen.cX 32
#kmisc_packarrs CertificateChecks.KernelHSStd.M12C.P CertificateChecks.KernelHSStd.M12PinGen.cP 72
#kmisc_packarrs CertificateChecks.KernelHSStd.M12C.CC CertificateChecks.KernelHSStd.M12PinGen.cCnt 32
#kmisc_packarrs CertificateChecks.KernelHSStd.M12C.H CertificateChecks.KernelHSStd.M12PinGen.hW 32

namespace CertificateChecks.KernelHSStd

open CFSG.KLie.CT (fget)

@[expose] noncomputable def M12.T (i : Nat) : Nat :=
  fget (M12.TP (Nat.shiftRight i (nat_lit 3))) (Nat.land i (nat_lit 7)) (nat_lit 72)

@[expose] noncomputable def M12.E (i : Nat) : Nat :=
  fget (M12.EP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 34)

@[expose] noncomputable def M12.S (i : Nat) : Nat :=
  fget (M12.SP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 17)

@[expose] noncomputable def M12.SI (i : Nat) : Nat :=
  fget (M12.SIP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 17)

@[expose] noncomputable def M12A.T (i : Nat) : Nat :=
  fget (M12A.TP (Nat.shiftRight i (nat_lit 3))) (Nat.land i (nat_lit 7)) (nat_lit 72)

@[expose] noncomputable def M12A.E (i : Nat) : Nat :=
  fget (M12A.EP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 20)

@[expose] noncomputable def M12A.S (i : Nat) : Nat :=
  fget (M12A.SP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 10)

@[expose] noncomputable def M12A.SI (i : Nat) : Nat :=
  fget (M12A.SIP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 10)

@[expose] noncomputable def M12B.T (i : Nat) : Nat :=
  fget (M12B.TP (Nat.shiftRight i (nat_lit 3))) (Nat.land i (nat_lit 7)) (nat_lit 72)

@[expose] noncomputable def M12B.E (i : Nat) : Nat :=
  fget (M12B.EP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 20)

@[expose] noncomputable def M12B.S (i : Nat) : Nat :=
  fget (M12B.SP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 10)

@[expose] noncomputable def M12B.SI (i : Nat) : Nat :=
  fget (M12B.SIP (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) (nat_lit 10)

@[expose] noncomputable def M12O.T (o j : Nat) : Nat :=
  nIf(Nat.beq o (nat_lit 0), M12A.T j, M12B.T j)

@[expose] noncomputable def M12O.N (o : Nat) : Nat :=
  nIf(Nat.beq o (nat_lit 0), nat_lit 396, nat_lit 495)

end CertificateChecks.KernelHSStd

end
