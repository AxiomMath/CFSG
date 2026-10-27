module

public import Certificates.Data.Kernel.Misc.Sp6RefS
public import Certificates.Kernel.Sp62.Rec
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS AX
  "Certificates/Kernel/Misc/Sp6RefS/data/ax.bin" 5 4 135 7102001942775831028
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS WX
  "Certificates/Kernel/Misc/Sp6RefS/data/wx.bin" 5 4 240 15991698892564856017
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS WP
  "Certificates/Kernel/Misc/Sp6RefS/data/wp.bin" 2 4 94 1054654120807854939
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS WC
  "Certificates/Kernel/Misc/Sp6RefS/data/wc.bin" 1 4 144 16695468909132768812
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS WM
  "Certificates/Kernel/Misc/Sp6RefS/data/wm.bin" 1 4 144 10706499106203682727
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS FR
  "Certificates/Kernel/Misc/Sp6RefS/data/fr.bin" 2 4 432 8488430060551071807
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS QI
  "Certificates/Kernel/Misc/Sp6RefS/data/qi.bin" 1 4 1296 8200572149387263950
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS RT
  "Certificates/Kernel/Misc/Sp6RefS/data/rt.bin" 2 4 7290 7196214541546214604
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS CX
  "Certificates/Kernel/Misc/Sp6RefS/data/cx.bin" 5 4 3240 9964504717823124720
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS CP
  "Certificates/Kernel/Misc/Sp6RefS/data/cp.bin" 4 4 2592 1323880011053062030
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS CS
  "Certificates/Kernel/Misc/Sp6RefS/data/cs.bin" 2 4 1296 2821430643073913343
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS OX
  "Certificates/Kernel/Misc/Sp6RefS/data/ox.bin" 5 4 11200 7947801122716117453
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS OP
  "Certificates/Kernel/Misc/Sp6RefS/data/op.bin" 4 4 8960 6685275986368135051
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS OS
  "Certificates/Kernel/Misc/Sp6RefS/data/os.bin" 2 4 4480 2491659700388778781
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS RR
  "Certificates/Kernel/Misc/Sp6RefS/data/rr.bin" 5 4 25920 11231368799914154348
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS RQ
  "Certificates/Kernel/Misc/Sp6RefS/data/rq.bin" 9 4 252 18414270972665545181
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp6RefS RC
  "Certificates/Kernel/Misc/Sp6RefS/data/rc.bin" 1 4 96 1757112274114957270

namespace CertificateChecks.KernelMisc.Sp6RefS

@[expose] noncomputable def ZG (i : Nat) : Nat :=
  Bool.rec (Bool.rec (nat_lit 38925369473) (nat_lit 34663842817) (Nat.beq i 1))
    (nat_lit 34630549640) (Nat.beq i 0)

@[expose] noncomputable def WG (i : Nat) : Nat :=
  Bool.rec (Bool.rec (nat_lit 17322483780) (nat_lit 34498166850) (Nat.beq i 1))
    (nat_lit 34628452488) (Nat.beq i 0)

@[expose] noncomputable def RS (k : Nat) : Nat :=
  Bool.rec (nat_lit 34498166850) (nat_lit 4565631105) (Nat.blt k 2)

@[expose] noncomputable def RI (k : Nat) : Nat :=
  Bool.rec (Bool.rec (Bool.rec (Bool.rec (nat_lit 13) (nat_lit 12) (Nat.beq k 3)) (nat_lit 1)
    (Nat.beq k 2)) (nat_lit 12) (Nat.beq k 1)) (nat_lit 9) (Nat.beq k 0)

@[expose] noncomputable def RW (k : Nat) : Nat :=
  Bool.rec (Bool.rec (Bool.rec (Bool.rec (nat_lit 3) (nat_lit 2) (Nat.beq k 3)) (nat_lit 1)
    (Nat.beq k 2)) (nat_lit 2) (Nat.beq k 1)) (nat_lit 1) (Nat.beq k 0)

@[expose] noncomputable def CG (l : Nat) : Nat :=
  Bool.rec (nat_lit 63241540540) (nat_lit 57860076019) (Nat.beq l 0)

@[expose] noncomputable def HG (l : Nat) : Nat :=
  Bool.rec (nat_lit 63746059761) (nat_lit 63455373516) (Nat.beq l 0)

@[expose] noncomputable def HI (l : Nat) : Nat :=
  Bool.rec (nat_lit 20258480036) (nat_lit 12739494157) (Nat.beq l 0)

@[expose] noncomputable def W7 : Nat := nat_lit 38959186952

@[expose] noncomputable def RG0 (g : Nat) : Nat :=
  Bool.rec (Bool.rec (nat_lit 21745568129) (nat_lit 51810224513) (Nat.beq g 1)) (nat_lit 7317102721)
    (Nat.beq g 0)

@[expose] noncomputable def RG2 (g : Nat) : Nat :=
  Bool.rec (Bool.rec (nat_lit 34498166850) (nat_lit 34630289049) (Nat.beq g 1)) (nat_lit 34681405569)
    (Nat.beq g 0)

@[expose] noncomputable def RG4 (g : Nat) : Nat :=
  Bool.rec (nat_lit 38384041657) (nat_lit 63608573885) (Nat.beq g 0)

@[expose] noncomputable def rqX (o i : Nat) : Nat := Nat.land (RQ (Nat.add o i)) CFSG.KD.Sp62.M36

@[expose] noncomputable def rqP (o i : Nat) : Nat := Nat.shiftRight (RQ (Nat.add o i)) 40

@[expose] noncomputable def recS (o p : Nat) : Nat :=
  CFSG.KD.Sp62.recX CFSG.KD.Sp62.REC o (CFSG.KD.Sp62.recF CFSG.KD.Sp62.REC o 2 p)

end CertificateChecks.KernelMisc.Sp6RefS
