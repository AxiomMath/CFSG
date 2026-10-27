module

public import Certificates.Kernel.Fin76bAut.Core
public import CFSG.Certificates.Kernel.Fin76bAut.Q
public import CFSG.Certificates.Kernel.Fin76bAut.Syl
public import CFSG.Certificates.Kernel.Fin76bAut.E613
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

universe u

namespace CertificateChecks.KernelFin76bAut

open CFSG.KS CFSG.KS.EAut CFSG.KS.PEnum CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.Fin76b.AutETable CFSG.EvenSporadicStandard.Fin76b.W16

theorem ch24614SylPt : ∀ i < 128, penumPtK 32 6 63 192 false (fun j => T (SP j))
    (fun j => T (SP j)) 5 128 ST SPL SPOS SSRT SSRI i = true := by
  have h := ch24614Syl
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  intro i hi
  simpa using penumSlK_spec h.2 i hi (by omega)

theorem eFacts615_of_mulE0 {G : Type u} [Group G] {E : Subgroup G} {t : G} {eltE : ℕ → G}
    (hL : ELabelling E t mulE0 eT eltE) : EFacts615 E t := by
  have h := ch24614Syl
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  exact eFacts615_of_checks hL ch24614ET ch24614RecOK ch24614Tup h.1 ch24614SylPt ch24614Ea

theorem eFacts613_of_mulE0 {G : Type u} [Group G] {E : Subgroup G} {t : G} {eltE : ℕ → G}
    (hL : ELabelling E t mulE0 eT eltE) : EFacts613 E t := by
  have h := ch24614Ker
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  exact eFacts613_of_checks hL ch24614ET ch24614RecOK (fun i hi => (ptK_spec (ch24614RecPt i hi)).1)
    ch24614Tup h.1 h.2 ch24614Inn ch24614Cls ch24614Fix ch24614Kl

theorem eFactsQ_of_mulE0 {G : Type u} [Group G] {E : Subgroup G} {t : G} {eltE : ℕ → G}
    (hL : ELabelling E t mulE0 eT eltE) : EFactsQ E t :=
  eFactsQ_of_checks hL ch24614ET ch24614RecOK ch24614Tup ch24614Inn ch24614Q

end CertificateChecks.KernelFin76bAut

end
