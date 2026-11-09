module

public import Certificates.Kernel.E6WK.Checks
public import Certificates.Kernel.TwE6Det.Chk0
public import Certificates.Kernel.TwE6Det.Chk1
public import Certificates.Kernel.TwE6Det.Chk2
public import CFSG.Certificates.Kernel.TwE6DetSound
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallTree
import all Certificates.Data.Kernel.E6WK
import all Certificates.Data.TwE6WeylKill

public section

namespace CertificateChecks.KernelTwE6Det

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.KC.TwE6Det CFSG.KD.E6WK
  CertificateChecks.KernelE6WK
open scoped Matrix

#kc_forall_tree ch1609001_all (fun i => chkAtT rtL up vtE6 i = true) 432
  CertificateChecks.KernelTwE6Det.ch1609001

theorem rtL_eq : rt vp = rtL := by
  have h : Nat.beq (rt vp) rtL = true := by quickRfl
  exact Nat.eq_of_beq_eq_true h

theorem vtE6_length : vtE6.length ≤ 16 := by
  decide +kernel

theorem covVT_vk : covVT vk vtE6 = true := by
  decide +kernel

theorem charpoly_two
    (v : WeylGroup TwistTag.E6.tag)
    (M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) :
    (13 ∣ (M.charpoly.eval (2 : ℤ)).natAbs → (M.charpoly.eval (2 : ℤ)).natAbs = 39) ∧
      (19 ∣ (M.charpoly.eval (2 : ℤ)).natAbs → (M.charpoly.eval (2 : ℤ)).natAbs = 57) :=
  charpoly_two_of_checks tab_check up_check k_check v_check up_wit_length.1 vtE6_length
    rtL_eq covVT_vk ch1609001_all v M hv

end CertificateChecks.KernelTwE6Det
