module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CertificateChecks.KernelM12Cover

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

theorem checkKernel_eq : checkKernel (enumeration fixedDQ) = true := by quickRfl

theorem checkPairs_eq : checkPairs (enumeration fixedDQ) = true := by quickRfl

theorem checkCount_eq : checkCount (enumeration fixedDQ) = true := by quickRfl

end CertificateChecks.KernelM12Cover

end
