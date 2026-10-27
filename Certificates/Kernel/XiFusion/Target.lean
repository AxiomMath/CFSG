module

public import Certificates.Certificate3016

public section

namespace CertificateChecks.KernelXiFusion

open CFSG.Monster.B.TwoA.Census CFSG.KC.SortTree CertificateChecks.Mono3016
  CertificateChecks.Batch3016

theorem target_rec : ∀ e ∈ xiEdges, e.target < 7 ∧
    ∃ t < sizes.getD e.target 0, valF 24 (recI (offs.getD e.target 0) t) =
      canI (permI e.normalizer (permI e.afterPerm e.afterSign)) := by
  decide +kernel

theorem target_mem :
    ∀ e ∈ xiEdges,
    canI (permI e.normalizer (permI e.afterPerm e.afterSign)) ∈ (monoCert e.target).pts.toList := by
  intro e he
  obtain ⟨ht, hx⟩ := target_rec e he
  exact Array.mem_toList_iff.2 (((facts _ ht).2.2.1 _).2 hx)

end CertificateChecks.KernelXiFusion

end
