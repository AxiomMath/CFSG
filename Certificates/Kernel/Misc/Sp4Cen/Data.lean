module

public import Certificates.Data.Kernel.Misc.Sp4Cen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen RI
  "Certificates/Kernel/Misc/Sp4Cen/data/ri.bin" 14 4 4424 4256491603094103276
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen LF
  "Certificates/Kernel/Misc/Sp4Cen/data/leaf.bin" 10 4 120 7015268899141165064
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen LC
  "Certificates/Kernel/Misc/Sp4Cen/data/lc.bin" 4 4 48 1031881472250178681
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen LW
  "Certificates/Kernel/Misc/Sp4Cen/data/lw.bin" 16 4 192 2745448060371791821
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen SBE
  "Certificates/Kernel/Misc/Sp4Cen/data/sbe.bin" 2 4 1440 7117946921960237745
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen SBP
  "Certificates/Kernel/Misc/Sp4Cen/data/sbp.bin" 4 4 2880 17804102693688128989
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen SBS
  "Certificates/Kernel/Misc/Sp4Cen/data/sbs.bin" 2 4 1440 15370316234314943765
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen SBC
  "Certificates/Kernel/Misc/Sp4Cen/data/sbc.bin" 2 4 2880 10003139993377281351
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen FM
  "Certificates/Kernel/Misc/Sp4Cen/data/fm.bin" 2 4 56 13370172698055489347
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen FG
  "Certificates/Kernel/Misc/Sp4Cen/data/fg.bin" 4 4 112 13164667786569136108
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen FP
  "Certificates/Kernel/Misc/Sp4Cen/data/fp.bin" 4 4 112 6843614100653817503
#kc_repo #kc_ktree CertificateChecks.KernelMisc.Sp4Cen FC
  "Certificates/Kernel/Misc/Sp4Cen/data/fc.bin" 1 4 56 5235589826953945614

namespace CertificateChecks.KernelMisc.Sp4Cen

@[expose] noncomputable def R0 : Nat := nat_lit 33833

@[expose] noncomputable def R1 : Nat := nat_lit 33957

@[expose] def REPS0 : List Nat := [5160]

@[expose] def REPS1 : List Nat := [7544, 8580]

@[expose] noncomputable def S0 : Nat := nat_lit 15938

@[expose] noncomputable def S1 : Nat := nat_lit 16237

@[expose] noncomputable def W0 : Nat := nat_lit 8580

@[expose] noncomputable def SG2 (j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) S1 S0 (Nat.beq j 0)

@[expose] noncomputable def F5 : Nat := nat_lit 40034

@[expose] noncomputable def F5I : Nat := nat_lit 29471

@[expose] noncomputable def X3 : Nat := nat_lit 27484

@[expose] noncomputable def X3I : Nat := nat_lit 61309

end CertificateChecks.KernelMisc.Sp4Cen

end
