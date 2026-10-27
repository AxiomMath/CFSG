module

public import Certificates.Kernel.Fi23Y.ChkDefs
public import Certificates.Kernel.Fi23K.Card
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi23Facts
public import Certificates.Certificate9111
public import Certificates.Certificate9206
import Certificates.Kernel.Fi23Y.KSFacts
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.F3.SepSpec
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Fi23.CertificateBase
public import CFSG.Sporadic.Fi23.SimpleBase
public import CFSG.Sporadic.Fi23.SlpSpec
public import CFSG.Sporadic.Presentation.Fi23
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec
public import Certificates.Certificate9206Base
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import Certificates.Kernel.Fi23K.Chain
public import Certificates.Kernel.Sporadic.Fi23Br.Words

public section

namespace CertificateChecks.KernelFi23Y

open CFSG.KC.Fi23Y CFSG.KD.Fi23Y CFSG.KD.Fi23S CFSG.KD.Fi23K
open CFSG.ComponentClassification.RankTwoSporadic.Fi23

theorem facts_of_K
    {cj wt : Nat → Nat} (hR : ∀ i < 3, rootY CFSG.KD.Fi23Y.GL CD LS wt i = true)
    (hP : ∀ r < 96, repY CD wt r = true) (hC : ∀ l < 262144, cenY CFSG.KD.Fi23Y.GL CD cj wt l = true)
    (hE : ∀ i < 3, ∀ r < 96, entY CFSG.KD.Fi23Y.GL TR CD wt i r = true) :
    Fi23CensusFactsOn Xc := by
  exact KSF.facts_of_checks hR hP hC hE

end CertificateChecks.KernelFi23Y

end
