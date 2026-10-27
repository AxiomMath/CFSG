module

public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Data
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Data
public import CFSG.RankThree.Native.FiveKit
meta import CFSG.RankThree.Native.FiveKit

set_option maxRecDepth 400000

#conj_orb CertificateChecks.KernelMisc.HS100.K3 CFSG.EvenSporadicStandard.HSStd.FiveY.hsGens 100 7
  CFSG.EvenSporadicStandard.HSStd.FiveY.hsKeys 1600
  roots CFSG.EvenSporadicStandard.HSStd.FiveY.x3
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.y0
  gens 3 2
