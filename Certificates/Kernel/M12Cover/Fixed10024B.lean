module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CertificateChecks.KernelM12Cover

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

theorem checkFour_eq : checkFour (enumeration fixedDQ) = true := by quickRfl

theorem checkInvolutions_eq : checkInvolutions (enumeration fixedDQ) = true := by quickRfl

theorem checkConj_eq : checkConj (enumeration fixedDQ) = true := by quickRfl

end CertificateChecks.KernelM12Cover

end
