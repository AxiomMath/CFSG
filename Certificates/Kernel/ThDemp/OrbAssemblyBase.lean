
module

public import CFSG.Certificates.Kernel.ThDemp.OrbBoundBase
public import CFSG.Sporadic.Th.SetupBase
public import Certificates.Kernel.ThDemp.Data
public import Certificates.Kernel.ThDemp.OrbData
public import Certificates.Kernel.ThDemp.OrbFam
import Certificates.Kernel.ThDemp.AssemblyBase
import Certificates.Kernel.ThDemp.OrbInv
import Certificates.Kernel.ThDemp.OrbB0
import Certificates.Kernel.ThDemp.OrbB1
import Certificates.Kernel.ThDemp.OrbB2
import Certificates.Kernel.ThDemp.OrbB3
import Certificates.Kernel.ThDemp.OrbB4
import Certificates.Kernel.ThDemp.OrbB5
import Certificates.Kernel.ThDemp.OrbB6
import Certificates.Kernel.ThDemp.OrbB7
import Certificates.Kernel.ThDemp.OrbB8
import Certificates.Kernel.ThDemp.OrbC
import Certificates.Kernel.ThDemp.OrbK
import Certificates.Kernel.ThDemp.OrbQ
import Certificates.Kernel.ThDemp.OrbE
import CFSG.Certificates.Kernel.Common.ForallTree

@[expose] public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp CFSG.KC.Th CFSG.KC.Th.Spec CFSG.Certificates.ThDemp CFSG.Sporadic.Th

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

#kc_forall_tree batch_all (fun k => bF k = true) 216 CertificateChecks.KernelThDemp.OrbB.s
#kc_forall_tree cross_all (fun k => cF k = true) 48 CertificateChecks.KernelThDemp.OrbC.s
#kc_forall_tree ky_all (fun k => kF k = true) 9 CertificateChecks.KernelThDemp.OrbK.s
#kc_forall_tree low_all (fun k => lF k = true) 9 CertificateChecks.KernelThDemp.OrbL.s

theorem sb_eq : ∀ i : Fin 9, lget orbData.sb i = OrbMain.sOf i := by decide +kernel

theorem words9_ne : lgetL orbData.words 9 ≠ [] := by decide +kernel

theorem orb_checks : Bound.OrbChecks dempData orbData where
  inv := inv_ok
  batch i hi y3 hy3 := by
    have hlt : 24 * i + y3 < 216 := by omega
    have h := batch_all (24 * i + y3) hlt
    have e1 : (24 * i + y3) / 24 = i := by omega
    have e2 : (24 * i + y3) % 24 = y3 := by omega
    change batchChk dempData orbData ((24 * i + y3) / 24) ((24 * i + y3) % 24) = true at h
    rwa [e1, e2] at h
  cross56 y3 hy3 := by
    have hlt : y3 < 48 := by omega
    have h := cross_all y3 hlt
    have e1 : y3 / 24 = 0 := by omega
    have e2 : y3 % 24 = y3 := by omega
    change crossChk dempData orbData (5 + 2 * (y3 / 24)) (6 + 2 * (y3 / 24)) (y3 % 24) = true at h
    rwa [e1, e2] at h
  cross78 y3 hy3 := by
    have hlt : 24 + y3 < 48 := by omega
    have h := cross_all (24 + y3) hlt
    have e1 : (24 + y3) / 24 = 1 := by omega
    have e2 : (24 + y3) % 24 = y3 := by omega
    change crossChk dempData orbData (5 + 2 * ((24 + y3) / 24)) (6 + 2 * ((24 + y3) / 24))
      ((24 + y3) % 24) = true at h
    rwa [e1, e2] at h
  ky i hi := ky_all i hi
  low i hi := low_all i hi
  orb := orb_ok
  codes := codes_ok
  elt1 := elt1_ok
  cent := cent_ok
  q := q_ok
  norm := norm_ok
  sb := sb_eq
  w9 := words9_ne

end CertificateChecks.KernelThDemp

end
