module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
public import CFSG.Sporadic.Co1Block.TwoBCheckInputs

public section

namespace CertificateChecks.KernelLC.Co1Cen2B

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
open CFSG.ComponentClassification.RankTwoSporadic.Co1

def hDag : List Rows × List Rows × Bool :=
  dag [twoBXYRows.1, twoBXYRows.2] (co1Cen2BH.map decWord)

def cDag : List Rows × List Rows × Bool := dag [aR, bR] (co1Cen2BC.map decWord)

end CertificateChecks.KernelLC.Co1Cen2B

end
