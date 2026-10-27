
module

public import Certificates.Kernel.L34Cov.LiftChecks
public import Certificates.Kernel.L34Cov.FieldR3
public import Certificates.Kernel.L34Cov.Glue
public import CFSG.Certificates.Kernel.L34Cov.LiftSound

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts

theorem lift_eq {uA uB : List (Fin 2 × Bool)}
    {L : List (List (Fin 2 × Bool) × List (Fin 2 × Bool) × ℕ)} (h : liftsK uA uB L = true)
    {p w : List (Fin 2 × Bool)} {e : ℕ} (hx : (p, w, e) ∈ L) :
    cv (p ++ substWord (autWs uA uB) w) = z₁ ^ (e % 48 / 12) * z₂ ^ (e % 12 / 3) * z₃ ^ (e % 3) :=
  liftsOK_sound vt_k modelA modelB h hx

theorem alphaF_eq (w : List (Fin 2 × Bool)) : alphaF w = [] ++ substWord (autWs uAF uBF) w := rfl

theorem facts22234 :
    (∀ s ∈ fieldZSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2))) ∧
    r3Idx.all (fun k => comp 42 (wordTab (tg k)) r₃T == comp 42 r₃T (wordTab (tg k))) = true := by
  refine ⟨fun s hs => ?_, ch22234r3_k⟩
  change cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  rw [cv_zword]
  simp only [fieldZSpecs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · dsimp only
    rw [alphaF_eq]
    exact (lift_eq ch22234l_k List.mem_cons_self).trans (by norm_num)
  · dsimp only
    rw [alphaF_eq]
    exact (lift_eq ch22234l_k (List.mem_cons_of_mem _ List.mem_cons_self)).trans (by norm_num)

end CertificateChecks.KernelL34Cov

end
