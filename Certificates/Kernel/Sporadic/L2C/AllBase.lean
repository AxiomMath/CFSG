
module

public import Certificates.Kernel.Sporadic.L2C.G2
public import Certificates.Kernel.Sporadic.L2C.G4
public import Certificates.Kernel.Sporadic.L2C.KB
public import Certificates.Kernel.Sporadic.L2C.KE0
public import Certificates.Kernel.Sporadic.L2C.KE1
public import Certificates.Kernel.Sporadic.L2C.KE2
public import Certificates.Kernel.Sporadic.L2C.KE3

@[expose] public section

#kon_join CertificateChecks.KernelSpor.L2CK.baseAll CertificateChecks.KernelSpor.L2CK.baseSl 9
#kon_join CertificateChecks.KernelSpor.L2CK.liftAll CertificateChecks.KernelSpor.L2CK.liftSl 9
#kon_join CertificateChecks.KernelSpor.L2CK.walkAll CertificateChecks.KernelSpor.L2CK.walkSl 10
#kon_join CertificateChecks.KernelSpor.L2CK.rowAll CertificateChecks.KernelSpor.L2CK.rowSl 90

namespace CertificateChecks.KernelSpor.L2CG

open CFSG.KC.Enum CertificateChecks.KernelSpor.L2CK
open CertificateChecks.KernelSpor.L2G (nblt slices)

theorem baseH : BaseH := slices (len := 315) (k := 9) (by norm_num) (by norm_num) baseAll

theorem liftH : LiftH := slices (len := 315) (k := 9) (by norm_num) (by norm_num) liftAll

theorem walkH : WalkH := fun x hx => by
  have h := slices (len := 300) (k := 10) (n := 2997) (by norm_num) (by norm_num) walkAll x hx
  rwa [show Nat.blt x 2997 = true from nblt.2 hx] at h

theorem rowH : RowH := fun u hu => by
  have h := slices (len := 100) (k := 90) (n := 8991) (by norm_num) (by norm_num) rowAll u hu
  rwa [show Nat.blt u 8991 = true from nblt.2 hu] at h

theorem lift_true : CFSG.Sporadic.SuzRecog.LevelTwoCover.coverLiftOK = true :=
  coverLiftOK_true baseH liftH

theorem deck_true : CFSG.Sporadic.SuzRecog.LevelTwoCover.coverDeckOK = true :=
  coverDeckOK_true baseH walkH kWord

theorem elim_true : CFSG.Sporadic.SuzRecog.LevelTwoCover.CoverElim := coverElim_of baseH rowH

theorem loc_true : CFSG.Sporadic.SuzRecog.LevelTwoCover.coverLocOK = true :=
  coverLocOK_true baseH kLoc

end CertificateChecks.KernelSpor.L2CG

end
