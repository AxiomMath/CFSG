
module

public import Certificates.Kernel.L34Cov.SigmaChecks
public import Certificates.Kernel.L34Cov.WordsGlue
public import Certificates.Kernel.L34W.Glue
public import CFSG.Certificates.Kernel.L34Cov.SigmaSound

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W CFSG.KC.L34Cov CertificateChecks.KernelL34W
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

theorem abPerm_uA_k {i : ℕ} (hi : i < 36) : abPerm (uA i) = repPerm i * aS * (repPerm i)⁻¹ :=
  (ab_spec gensG ch22219ab_k uA_eq uB_eq hi).1

theorem abPerm_uB_k {i : ℕ} (hi : i < 36) : abPerm (uB i) = repPerm i * bS * (repPerm i)⁻¹ :=
  (ab_spec gensG ch22219ab_k uA_eq uB_eq hi).2

theorem conj_tg_k {i k : ℕ} (hi : i < 36) (hk : k < 64) : (alphaEntry i k).1 < 64 ∧
    repPerm i * wordPerm (tg k) * (repPerm i)⁻¹ = wordPerm (tg (alphaEntry i k).1) :=
  cj_spec gensG y_k alOf bounds_k ch22219cj_k hi hk

theorem exists_decomp_k {y : Equiv.Perm (Fin 42)} (hy : y ∈ R)
    (hN : ∀ t ∈ T0, y * t * y⁻¹ ∈ T0) : ∃ i < 36, ∃ t < 64, y = wordPerm (tg t) * repPerm i :=
  exists_decomp_of gensG y_k ch22219fix_k ch22219orb_k ch22219stab_k ch22219sort_k hy hN

end CertificateChecks.KernelL34Cov

end
