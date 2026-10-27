module

public import Certificates.Kernel.Misc.Perm.Bloom13B
public import Certificates.Kernel.Misc.Perm.Bloom13C

public section

namespace CertificateChecks.KernelMisc.Bloom13

open CFSG.RankThree.PartTwo.Toolkit CFSG.RankThree.PartTwo.Toolkit.Raw
open CFSG.KC.Misc.Clos (allR allR_iff forall_of_chunks)

theorem hall : (List.range 19683).all (bloom13At (code cR) f0Codes nfMask coverMask) = true := by
  have hc : ∀ c < 9, allR (2187 * c) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by
    intro c hc
    interval_cases c
    exacts [chunk0, chunk1, chunk2, chunk3, chunk4, chunk5, chunk6, chunk7, chunk8]
  have hcR : code cR = 2466 := by decide
  rw [hcR, hf0, hnf, hcv, List.all_eq_true]
  intro c hc'
  exact forall_of_chunks 2187 9 _ hc c (List.mem_range.1 hc')

theorem facts : bloom13Check = true := by
  rw [bloom13Check, q1, q2, q3, hall, q4, q5, trees]
  rfl

end CertificateChecks.KernelMisc.Bloom13

end
