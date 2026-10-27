module

public import Certificates.Kernel.P1L43.FbarMain
public import Certificates.Kernel.P1L43.FbarOuter

public section

namespace CertificateChecks.K442264

open CFSG.ComponentClassification.HarrisLit.P1.L43 CFSG.ComponentClassification.HarrisLit.P1
open Certificates.Asc82Fbar

theorem fbarCheck_true :
    fbarCheck 80 100000 l43Sift l43Runs (fbarInner ()) (fbarOuter ()) = true := by
  unfold fbarCheck
  rw [List.all_eq_true]
  intro R hR
  rw [List.all_eq_true]
  intro r hr
  simp only [l43Runs, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · simp only [runuD, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact inner_true
    · rfl
    · rfl
  · simp only [runuS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [runuDS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rfl
    · rfl
    · exact outer_true

end CertificateChecks.K442264

end
