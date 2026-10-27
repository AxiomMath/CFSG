module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData

public section

namespace CertificateChecks.KernelLC.Co1End

open CFSG.Sporadic.Co1Schreier.Native CFSG.ComponentClassification.RankTwoSporadic.Co1

def endDag : List Rows × List Rows × Bool := dag co1EndBase (co1EndD.map decWord)

end CertificateChecks.KernelLC.Co1End

end
