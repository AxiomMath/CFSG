module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35ECertInputs

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts

theorem ch22234r3_k :
    r3Idx.all (fun k => comp 42 (wordTab (tg k)) r₃T == comp 42 r₃T (wordTab (tg k))) = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
