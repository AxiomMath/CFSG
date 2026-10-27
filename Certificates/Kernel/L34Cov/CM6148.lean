module

public import Certificates.Kernel.L34Cov.CM6148Checks
public import Certificates.Kernel.L34Cov.Glue
public import CFSG.Certificates.Kernel.L34Cov.NfLiftSound

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.OddStandard.ONanRec.IdCM

theorem nfOf_eq (L : List (Fin 6 × Bool)) :
    nfOf L = L.foldl (nfStepA (substWord (autWs uAU uBU)) genW) ([], false) := rfl

theorem cm_eq {l : List (Fin 6 × Bool)} {s : List (Fin 2 × Bool)}
    {e : ℕ} (hx : (l, s, e) ∈ cmL) :
    cv ((nfOf l).1 ++ s) = z₁ ^ (e % 48 / 12) * z₂ ^ (e % 12 / 3) * z₃ ^ (e % 3) := by
  rw [nfOf_eq]
  exact nfLiftsOK_sound vt_k modelA modelB ch6148l_k hx

theorem code6148_spec : ∀ d ∈ relData, code6148 d.2 % 48 / 12 = d.2.1 ∧
    code6148 d.2 % 12 / 3 = d.2.2.1 ∧ code6148 d.2 % 3 = d.2.2.2 := by
  decide

theorem facts6148 :
    (∀ d ∈ relData, (nfOf d.1.toWord).2 = false) ∧ (nfOf invA).2 = false ∧
    (nfOf invB).2 = false ∧ (nfOf invU).2 = true ∧
    ∀ s ∈ cmSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2)) := by
  have hp := ch6148p_k
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  refine ⟨h1, h2, h3, h4, fun s hs => ?_⟩
  change cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  rw [cv_zword]
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    have hx : (d.1.toWord, ([] : List (Fin 2 × Bool)), code6148 d.2) ∈ cmL :=
      List.mem_append_left _ (List.mem_map_of_mem (f := fun d : FreeGroup (Fin 6) × ℕ × ℕ × ℕ =>
        (d.1.toWord, ([] : List (Fin 2 × Bool)), code6148 d.2)) hd)
    have h := cm_eq hx
    rw [List.append_nil] at h
    obtain ⟨c1, c2, c3⟩ := code6148_spec d hd
    rw [c1, c2, c3] at h
    exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    have m : ∀ x ∈ [(invA, [((0 : Fin 2), false)], 1), (invB, [((1 : Fin 2), false)], 18),
        (invU, ([] : List (Fin 2 × Bool)), 0)], x ∈ cmL := fun x hx => List.mem_append_right _ hx
    rcases hs with rfl | rfl | rfl
    · exact (cm_eq (m _ List.mem_cons_self)).trans (by norm_num)
    · exact (cm_eq (m _ (List.mem_cons_of_mem _ List.mem_cons_self))).trans (by norm_num)
    · have h := cm_eq (m _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      rw [List.append_nil] at h
      exact h.trans (by norm_num)

end CertificateChecks.KernelL34Cov

end
