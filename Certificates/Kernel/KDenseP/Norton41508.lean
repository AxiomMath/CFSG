module

public import Certificates.Kernel.KDenseP.Norton
public import CFSG.Certificates.Kernel.KDenseP.Norton.C41508
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ElevenRotCheckDefs

public section

namespace CertificateChecks.KernelKDenseP.Norton41508

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Norton CertificateChecks.KernelKDenseP.Axis
  CertificateChecks.KernelKDenseP.TwoPoint CertificateChecks.KernelKDenseP.Norton
  CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

set_option maxRecDepth 100000

theorem c41508 : elevenRotCheck () = true := by
  have h := (kd_nrtK% CFSG.KD.NRT.c41508 e41508 []).1
  simp only [e41508, agreeAll, List.all_cons, List.all_nil, Bool.and_true] at h
  simp only [elevenRotCheck, agreeC_eq]
  exact h

end CertificateChecks.KernelKDenseP.Norton41508

end
