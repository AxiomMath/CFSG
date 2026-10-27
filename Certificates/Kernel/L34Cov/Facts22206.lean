module

public import Certificates.Kernel.L34Cov.Cover2Checks
public import Certificates.Kernel.L34Cov.Glue
public import Certificates.Kernel.L34W.Glue
public import CFSG.Certificates.Kernel.L34Cov.TransSound

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CertificateChecks.KernelL34W

theorem comm22206_spec {d : ℕ × ℕ × ℕ × ℕ × ℕ}
    (hd : d ∈ commData2) :
    cv (commWord (tw d.1) (tw d.2.1)) = cv (zword d.2.2.1 d.2.2.2.1 d.2.2.2.2) := by
  rw [cv_zword]
  have hs : d ∈ commData2.take 265 ∨ d ∈ commData2.drop 265 := by
    rw [← List.mem_append, List.take_append_drop]
    exact hd
  rcases hs with hs | hs
  · exact cv_eq_of_cvId (List.all_eq_true.1 ch22206w_a d hs)
  · exact cv_eq_of_cvId (List.all_eq_true.1 ch22206w_b d hs)

theorem even22206 :
    commData2.all (fun d => (d.2.2.1 == 0 || d.2.2.1 == 2) && (d.2.2.2.1 == 0 || d.2.2.2.1 == 2)) =
      true := by
  have h := ch22206c_1
  unfold cOK1 at h
  rw [List.all_eq_true] at h ⊢
  intro d hd
  have h' := h d hd
  rw [Bool.and_eq_true] at h'
  exact h'.1

theorem facts22206 :
    (∀ s ∈ cover2Specs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2))) ∧
    commData2.all (fun d => (d.2.2.1 == 0 || d.2.2.1 == 2) && (d.2.2.2.1 == 0 || d.2.2.2.1 == 2)) =
      true ∧
    transOK = true ∧ cceOK = true := by
  refine ⟨fun s hs => ?_, even22206, transOK_of_transK ch22206c_1 ch22206c_2 ch22206c_t,
    cceOK_of_cceK gensG ch22206c_1 ch22206c_2 ch22206c_c⟩
  change cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    exact comm22206_spec hd
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    rw [cv_zword]
    exact cv_eq_of_cvId (List.all_eq_true.1 ch22206w_f d hd)

end CertificateChecks.KernelL34Cov

end
