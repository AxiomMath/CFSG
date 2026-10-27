module

public import Certificates.Kernel.Fin76bAut.Rec
public import Certificates.Kernel.Fin76bAut.TabFacts
public import CFSG.Certificates.Kernel.Fin76bAut.Cent
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

universe u

namespace CertificateChecks.KernelFin76bAut

open CFSG.KS CFSG.KS.EAut CFSG.KS.PEnum CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.Fin76b.AutETable CFSG.EvenSporadicStandard.Fin76b.W16

theorem ch24614RecOK : RecOK.{u} ET 1920 T :=
  recOK_of_checks ch24614Hd ch24614RecPt ch24614Tup

theorem ch24614ET : ∀ a < 32, ∀ b < 32, mulE0 a b = eMul ET a b := fun a ha b hb =>
  (eTabK_spec ch24614Tab a ha b hb).symm

theorem eFacts69_of_mulE0 {G : Type u} [Group G] {E : Subgroup G} {t : G} {eltE : ℕ → G}
    (hL : ELabelling E t mulE0 eT eltE) : EFacts69 E t := by
  have h := ch24614Sq
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  exact eFacts69_of_checks hL ch24614ET ch24614RecOK ch24614E69Tab h.1 (by norm_num) h.2
    (by norm_num)

theorem eFacts611_of_mulE0 {G : Type u} [Group G] {E : Subgroup G} {t : G} {eltE : ℕ → G}
    (hL : ELabelling E t mulE0 eT eltE) : EFacts611 E t :=
  eFacts611_of_checks hL ch24614ET ch24614RecOK ch24614Tup ch24614Pair

theorem eFacts614_of_mulE0 {G : Type u} [Group G] {E : Subgroup G} {t : G} {eltE : ℕ → G}
    (hL : ELabelling E t mulE0 eT eltE) : EFacts614 E t :=
  eFacts614_of_checks hL ch24614ET ch24614RecOK (fun i hi => (ptK_spec (ch24614RecPt i hi)).1)
    ch24614Tup ch24614Cls ch24614Cent

end CertificateChecks.KernelFin76bAut

end
