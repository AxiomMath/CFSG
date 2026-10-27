module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2CTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2CData

public section

namespace CertificateChecks.KernelLC.Co1Cen2C

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
open CFSG.ComponentClassification.RankTwoSporadic.Co1

def globDag : List Rows × List Rows × Bool := dag co1Cen2CBase (co1Cen2CGlobal.map decWord)

def pw1Dag : List Rows × List Rows × Bool :=
  dag (entriesR co1Cen2CBase (co1Cen2CGlobal.map decWord) co1Cen2CS1) (co1Cen2CD1.map decWord)

def pw2Dag : List Rows × List Rows × Bool :=
  dag (entriesR co1Cen2CBase (co1Cen2CGlobal.map decWord) co1Cen2CS2) (co1Cen2CD2.map decWord)

def rDag : List Rows × List Rows × Bool :=
  dag (entriesR co1Cen2CBase (co1Cen2CGlobal.map decWord) co1Cen2CS1 ++
    entriesR co1Cen2CBase (co1Cen2CGlobal.map decWord) co1Cen2CS2) (co1Cen2CRD.map decWord)

end CertificateChecks.KernelLC.Co1Cen2C

end
