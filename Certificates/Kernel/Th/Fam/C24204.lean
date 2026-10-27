module

public import Certificates.Kernel.Th.Fam.K
public import Certificates.Kernel.Th.Fam.LocalTE
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvData

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CertificateChecks.KernelTh.Fam.Local

@[expose] def commT (u v : TE) : TE × TE × Bool := (.mul u v, .mul v u, true)

@[expose] def l24204 : List (TE × TE × Bool) :=
  [commT g1T g2T, commT g1T g3T, commT g1T g4T, commT g2T g3T, commT g2T g4T, commT g3T g4T,
    (.mul g1T g1T, aelT 2, true), (.mul g2T g2T, aelT 1, true), (.mul g3T g3T, aelT 5, true),
    (.mul g4T g4T, aelT 10, true),
    commT g1T .z, commT g1T a1T, commT g1T a2T, commT g1T a3T,
    commT g2T .z, commT g2T a1T, commT g2T a2T, commT g2T a3T,
    commT g3T .z, commT g3T a1T, commT g3T a2T, commT g3T a3T,
    commT g4T .z, commT g4T a1T, commT g4T a2T, commT g4T a3T,
    commT beT .z, commT beT a1T, commT beT a2T, commT beT a3T,
    (.mul beT beT, .one, true),
    (.mul (.mul beT g1T) beT, .mul g1T (.mul g1T g1T), true),
    (.mul (.mul beT g2T) beT, .mul g2T (.mul g2T g2T), true),
    (.mul (.mul beT g3T) beT, .mul g3T (.mul g3T g3T), true),
    (.mul (.mul beT g4T) beT, .mul g4T (.mul g4T g4T), true)]

theorem ok24204 : pairsOK thK l24204 = true := by quickRfl

end CertificateChecks.KernelTh.Fam

end
