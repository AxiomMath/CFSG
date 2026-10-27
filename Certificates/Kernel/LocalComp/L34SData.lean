module

public import Certificates.Kernel.LocalComp.L34Gen2
public import Certificates.Data.Kernel.L34K
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.LocalComp.L34Gen2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34X

open CFSG.KLie.CT (fget)

@[expose] noncomputable def at8 (F : Nat → Nat) (w i : Nat) : Nat :=
  fget (F (Nat.shiftRight i (nat_lit 3))) (Nat.land i (nat_lit 7)) w

@[expose] noncomputable def at16 (F : Nat → Nat) (w i : Nat) : Nat :=
  fget (F (Nat.shiftRight i (nat_lit 4))) (Nat.land i (nat_lit 15)) w

end CertificateChecks.KernelLC.L34X

#kmisc_packarrs CertificateChecks.KernelLC.L34S.TP CertificateChecks.KernelLC.L34Gen.sT 252
#kmisc_packarrs CertificateChecks.KernelLC.L34S.EP CertificateChecks.KernelLC.L34Gen.sE 54
#kmisc_packarrs CertificateChecks.KernelLC.L34S.SP CertificateChecks.KernelLC.L34Gen.sS 18
#kmisc_packarrs CertificateChecks.KernelLC.L34S.SIP CertificateChecks.KernelLC.L34Gen.sSI 18
#kmisc_packarrs CertificateChecks.KernelLC.L34S.C CertificateChecks.KernelLC.L34Gen.sC 32

#kmisc_packarrs CertificateChecks.KernelLC.L34O0.TP CertificateChecks.KernelLC.L34Gen.o0T 252
#kmisc_packarrs CertificateChecks.KernelLC.L34O0.EP CertificateChecks.KernelLC.L34Gen.o0E 66
#kmisc_packarrs CertificateChecks.KernelLC.L34O0.SP CertificateChecks.KernelLC.L34Gen.o0S 18
#kmisc_packarrs CertificateChecks.KernelLC.L34O0.SIP CertificateChecks.KernelLC.L34Gen.o0SI 18
#kmisc_packarrs CertificateChecks.KernelLC.L34O1.TP CertificateChecks.KernelLC.L34Gen.o1T 252
#kmisc_packarrs CertificateChecks.KernelLC.L34O1.EP CertificateChecks.KernelLC.L34Gen.o1E 66
#kmisc_packarrs CertificateChecks.KernelLC.L34O1.SP CertificateChecks.KernelLC.L34Gen.o1S 18
#kmisc_packarrs CertificateChecks.KernelLC.L34O1.SIP CertificateChecks.KernelLC.L34Gen.o1SI 18
#kmisc_packarrs CertificateChecks.KernelLC.L34O2.TP CertificateChecks.KernelLC.L34Gen.o2T 252
#kmisc_packarrs CertificateChecks.KernelLC.L34O2.EP CertificateChecks.KernelLC.L34Gen.o2E 66
#kmisc_packarrs CertificateChecks.KernelLC.L34O2.SP CertificateChecks.KernelLC.L34Gen.o2S 18
#kmisc_packarrs CertificateChecks.KernelLC.L34O2.SIP CertificateChecks.KernelLC.L34Gen.o2SI 18
#kmisc_packarrs CertificateChecks.KernelLC.L34O3.TP CertificateChecks.KernelLC.L34Gen.o3T 252
#kmisc_packarrs CertificateChecks.KernelLC.L34O3.EP CertificateChecks.KernelLC.L34Gen.o3E 66
#kmisc_packarrs CertificateChecks.KernelLC.L34O3.SP CertificateChecks.KernelLC.L34Gen.o3S 18
#kmisc_packarrs CertificateChecks.KernelLC.L34O3.SIP CertificateChecks.KernelLC.L34Gen.o3SI 18

#kmisc_packarrs CertificateChecks.KernelLC.L34X.GI CertificateChecks.KernelLC.L34Gen.giP 8
#kmisc_packarrs CertificateChecks.KernelLC.L34X.RP CertificateChecks.KernelLC.L34Gen.rP 8
#kmisc_packarrs CertificateChecks.KernelLC.L34X.NWP CertificateChecks.KernelLC.L34Gen.normW 8

#kmisc_packarrs CertificateChecks.KernelLC.L34C1.P CertificateChecks.KernelLC.L34Gen.c1P 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C1.X CertificateChecks.KernelLC.L34Gen.c1X 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C2.P CertificateChecks.KernelLC.L34Gen.c2P' 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C2.X CertificateChecks.KernelLC.L34Gen.c2X 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C3.P CertificateChecks.KernelLC.L34Gen.c3P' 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C3.X CertificateChecks.KernelLC.L34Gen.c3X 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C4.P CertificateChecks.KernelLC.L34Gen.c4P 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C4.X CertificateChecks.KernelLC.L34Gen.c4X 8

#kmisc_packarrs CertificateChecks.KernelLC.L34C2.I CertificateChecks.KernelLC.L34Gen.c2I 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C2.Q CertificateChecks.KernelLC.L34Gen.c2Q 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C2.CP CertificateChecks.KernelLC.L34Gen.c2P 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C2.L CertificateChecks.KernelLC.L34Gen.c2L 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C3.I CertificateChecks.KernelLC.L34Gen.c3I 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C3.Q CertificateChecks.KernelLC.L34Gen.c3Q 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C3.CP CertificateChecks.KernelLC.L34Gen.c3P 8
#kmisc_packarrs CertificateChecks.KernelLC.L34C3.L CertificateChecks.KernelLC.L34Gen.c3L 8

#kmisc_packarrs CertificateChecks.KernelLC.L34C4.I CertificateChecks.KernelLC.L34Gen.c4I 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D1.P CertificateChecks.KernelLC.L34Gen.d1P 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D1.I CertificateChecks.KernelLC.L34Gen.d1I 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D1.PW CertificateChecks.KernelLC.L34Gen.d1Prod 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D1.M CertificateChecks.KernelLC.L34Gen.d1Misc 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D1.CW CertificateChecks.KernelLC.L34Gen.d1Comm 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D2.P CertificateChecks.KernelLC.L34Gen.d2P 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D2.I CertificateChecks.KernelLC.L34Gen.d2I 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D2.PW CertificateChecks.KernelLC.L34Gen.d2Prod 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D2.M CertificateChecks.KernelLC.L34Gen.d2Misc 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D2.CW CertificateChecks.KernelLC.L34Gen.d2Comm 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D3.P CertificateChecks.KernelLC.L34Gen.d3P 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D3.PW CertificateChecks.KernelLC.L34Gen.d3Prod 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D3.M CertificateChecks.KernelLC.L34Gen.d3Misc 8
#kmisc_packarrs CertificateChecks.KernelLC.L34D3.CW CertificateChecks.KernelLC.L34Gen.d3Comm 8

end
