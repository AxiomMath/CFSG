module

public import Certificates.Kernel.Misc.StrsCodes
public import Certificates.Data.Kernel.L34Cov.Codes
public import Certificates.Data.GrSLitL34FactsRealReps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
meta import Certificates.Data.GrSLitL34FactsRealReps
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Open.Defs
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
meta import CFSG.Open.Defs

public section

#ks_strs_codes CertificateChecks.KernelL34Cov.TwC
  CFSG.ComponentClassification.GrSLit.L34Facts.twStrings CFSG.KC.L34Cov.decC "aAbB"

#ks_strs_codes CertificateChecks.KernelL34Cov.UAC
  (CFSG.ComponentClassification.GrSLit.L34Facts.Real.realRepU.map Prod.fst) CFSG.KC.L34Cov.decC
  "aAbB"

#ks_strs_codes CertificateChecks.KernelL34Cov.UBC
  (CFSG.ComponentClassification.GrSLit.L34Facts.Real.realRepU.map Prod.snd) CFSG.KC.L34Cov.decC
  "aAbB"

namespace CertificateChecks.KernelL34Cov

open CFSG.KC.L34Cov

theorem codes_k : TwC.codes.length = 64 ∧ TwC.codes.all codesOK = true ∧
    UAC.codes.length = 36 ∧ UAC.codes.all codesOK = true ∧
    UBC.codes.length = 36 ∧ UBC.codes.all codesOK = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
