module

public import Certificates.Data.Kernel.SmithD6.T2Data
public import Certificates.Data.Kernel.SmithD6.T2Defs

public section

namespace CertificateChecks.SmithD6T2

open CFSG.KC.SmithD6T2 CFSG.KD.SmithD6T2

theorem ptTree_ok : d6PtTreeOK ptD ptG = true := by decide +kernel

theorem rsTree_ok : d6RsTreeOK rsD rsG = true := by decide +kernel

theorem split_ok : d6SplitOK spS = true := by decide +kernel

theorem ptCnt_eq : d6PtCnt = 2079 := by decide +kernel

theorem rsCnt_eq : d6RsCnt = 1054 := by decide +kernel

end CertificateChecks.SmithD6T2

end
