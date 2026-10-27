module

public import Certificates.Kernel.J4Q.D4Rep
public import Certificates.Kernel.J4Q.D4L
public import Certificates.Kernel.J4Q.D4H

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KD.J4Q CFSG.QuasithinUnique.A5

theorem d4_grp_b : Dec2.chkGrp b1344Words = true :=
  grp_of b1344Words B1G b1_hG (by rw [b1344Words_eq]; rfl) b1_grp

theorem d4_grp_a : Dec2.chkGrp a85Words = true :=
  grp_of a85Words A8G a8_hG (by rw [a85Words_eq]; rfl) a8_grp

theorem d4_all : chkD4 d4Reps d4Words d4Wit [b1344Words, a85Words] = true :=
  d4_of D4RA.all (cells_of D4LA.all) D4HA.all reps_wf

end CertificateChecks.KernelJ4Q

end
