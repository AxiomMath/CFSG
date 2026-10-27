
module

public import Certificates.Kernel.ThDemp.AssemblyBase

public import CFSG.Certificates.Kernel.ThDemp.Sound
public import CFSG.Sporadic.Th.Setup
public import Certificates.Kernel.ThDemp.Data
import Certificates.Kernel.ThDemp.Slp
import Certificates.Kernel.ThDemp.Shape
import Certificates.Kernel.ThDemp.Lev
import Certificates.Kernel.ThDemp.Res0
import Certificates.Kernel.ThDemp.Res1
import Certificates.Kernel.ThDemp.Res2
import Certificates.Kernel.ThDemp.Res3
import Certificates.Kernel.ThDemp.Res4
import Certificates.Kernel.ThDemp.Res5
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Checks2.Seed_S

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp CFSG.KC.Th CFSG.Certificates.ThDemp CFSG.Sporadic.Th

theorem dempwolff_card :
    ∃ d : J, ((d : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) =
        CFSG.KC.Th.Spec.pkMat (dempData.RB (BigS.regAt dempData.rd 1)) ∧
      Nat.card (Subgroup.closure ({a, d} : Set J)) = 319979520 := by
  have hF := dempChk_facts dempData demp_chk
  obtain ⟨d₀, d₁, h₀, h₁, hc⟩ := card_closure_eq hF (a := a) (b := b)
    (by rw [a_val, pkMat_SA]) (by rw [b_val, pkMat_SB])
  have e : d₀ = a := by
    apply Subtype.ext
    apply Units.ext
    rw [h₀, rd_zero, hF.rb1, pkMat_SA, a_val]
  subst e
  exact ⟨d₁, h₁, hc⟩

end CertificateChecks.KernelThDemp

end
