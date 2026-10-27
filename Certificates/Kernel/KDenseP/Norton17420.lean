module

public import Certificates.Kernel.KDenseP.Norton
public import CFSG.Certificates.Kernel.KDenseP.Norton.C17420
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ElevenX5Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.AgreeTasks

public section

namespace CertificateChecks.KernelKDenseP.Norton17420

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Norton CertificateChecks.KernelKDenseP.Axis
  CertificateChecks.KernelKDenseP.TwoPoint CertificateChecks.KernelKDenseP.Norton
  CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Dickson.I271

set_option maxRecDepth 100000

theorem c17420 : elevenX5yCheck () = true := by
  have h := (kd_nrtK% CFSG.KD.NRT.c17420 e17420 []).1
  simp only [e17420, agreeAll, List.all_cons, List.all_nil, Bool.and_true] at h
  simp only [elevenX5yCheck, agreeC_eq]
  exact h

end CertificateChecks.KernelKDenseP.Norton17420

end
