module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2ATests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2AData

public section

namespace CertificateChecks.KernelLC.Co1Cen2A

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
open CFSG.ComponentClassification.RankTwoSporadic.Co1

def iotaDag : List Rows × List Rows × Bool := dag [hRows0, hRows1] iotaDerivs

def globDag : List Rows × List Rows × Bool := dag co1Cen2ABase (co1Cen2AGlobal.map decWord)

def pw1Dag : List Rows × List Rows × Bool :=
  dag (entriesR co1Cen2ABase (co1Cen2AGlobal.map decWord) co1Cen2AS1) (co1Cen2AD1.map decWord)

def pw2Dag : List Rows × List Rows × Bool :=
  dag (entriesR co1Cen2ABase (co1Cen2AGlobal.map decWord) co1Cen2AS2) (co1Cen2AD2.map decWord)

def qDag : List Rows × List Rows × Bool :=
  dag (entriesR co1Cen2ABase (co1Cen2AGlobal.map decWord) co1Cen2AS1 ++
    entriesR co1Cen2ABase (co1Cen2AGlobal.map decWord) co1Cen2AS2) (co1Cen2AQD.map decWord)

end CertificateChecks.KernelLC.Co1Cen2A

end
