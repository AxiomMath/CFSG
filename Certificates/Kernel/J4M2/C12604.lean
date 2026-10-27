module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSCentralData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSCentralData
public import Certificates.Kernel.J4M2.C12604Checks
public import Certificates.Kernel.SporSch.J4S11.Facts
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4JS

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4E CFSG.Sporadic.J4Schreier
  CertificateChecks.KernelSporSch.J4E7 CertificateChecks.KernelJ4Gam

theorem pJS : PairOK jsJn JP.1 JP.2 := powP_ok hK hH2 20

theorem pSS : PairOK jsSn SP.1 SP.2 :=
  powP_ok hK (mulP_ok hK (powP_ok hK hH1 2) (powP_ok hK hH2 5)) 11

theorem pQS : PairOK jsQn QP.1 QP.2 := mulP_ok hK (powP_ok hK hQX 8) (powP_ok hK hQY 4)

theorem jsOK_ok : jsOK = true := by
  have hj := fj
  obtain ⟨wPJ, ePJ⟩ := pack_enc pj
  obtain ⟨wIJ, eIJ⟩ := pack_enc ij
  obtain ⟨wRJ, eRJ⟩ := pack_enc rj
  rw [← pJS.1.2, ← ePJ, ← eIJ, ← eRJ] at hj
  have hs := fs
  obtain ⟨wPS, ePS⟩ := pack_enc ps
  obtain ⟨wIS, eIS⟩ := pack_enc iS
  obtain ⟨wRS, eRS⟩ := pack_enc rs
  rw [← pSS.1.2, ← ePS, ← eIS, ← eRS] at hs
  unfold jsOK
  rw [fixK_sound hK pJS.1.1 wPJ wIJ wRJ (by norm_num) hj,
    fixK_sound hK pSS.1.1 wPS wIS wRS (by norm_num) hs]
  rfl

theorem centralOK_ok : centralOK = true := by
  have h1 := jj
  rw [← pJS.1.2] at h1
  have h2 := ss
  rw [← pSS.1.2] at h2
  have h3 := sq
  rw [← pSS.1.2, ← pQS.1.2] at h3
  unfold centralOK
  simp only [Bool.and_eq_true]
  exact ⟨⟨eq_one_sound hK pJS.1.1 pJS.1.1 h1, eq_one_sound hK pSS.1.1 pSS.1.1 h2⟩,
    eq_sound hK pSS.1.1 pQS.1.1 pQS.1.1 pSS.1.1 h3⟩

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier in
theorem c12604 : jsOK = true := jsOK_ok

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier in
theorem c12606 : centralOK = true := centralOK_ok

end CertificateChecks.KernelJ4JS

end
