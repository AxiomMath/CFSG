module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CertificateChecks.KernelM12Cover

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

theorem checkChainD_eq : checkChainD = true := by quickRfl

theorem checkFourMul_eq : checkFourMul = true := by quickRfl

theorem checkFourInv_eq : checkFourInv = true := by quickRfl

theorem checkFourAbelian_eq : checkFourAbelian = true := by quickRfl

theorem checkFourDistinctEntries_eq : checkFourDistinctEntries = true := by quickRfl

theorem checkFourSeparated_eq : checkFourSeparated = true := by quickRfl

theorem checkFourArrays_eq : checkFourArrays = true := by quickRfl

theorem checkFourWords_eq : checkFourWords = true := by quickRfl

theorem checkFourIndex_eq : checkFourIndex = true := by quickRfl

end CertificateChecks.KernelM12Cover

end
