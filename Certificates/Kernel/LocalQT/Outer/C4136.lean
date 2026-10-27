module

public import CFSG.Certificates.Kernel.LocalQTOuterSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22OuterInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Data
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4136

open CFSG.KC.LQT.W CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def cG : List Nat := [228952723507329932679484465855724, 81506110577382089737470578414133]

theorem hG : [m22gA, m22gB].map codeP = cG := by decide +kernel
theorem hr₁ : codeP m22OutRep1 = 384659559006726606297335784869005 := by decide +kernel
theorem hr₂ : codeP m22OutRep2 = 25951403204182264746614498855445 := by decide +kernel
theorem k₁ : outerC 22 384659559006726606297335784869005 cG (m22OuterK.getD 0 ([], [])).1
    (m22OuterK.getD 0 ([], [])).2 = true := by quickRfl
theorem k₂ : outerC 22 25951403204182264746614498855445 cG (m22OuterK.getD 1 ([], [])).1
    (m22OuterK.getD 1 ([], [])).2 = true := by quickRfl

end CFSG.KD.LQT.C4136

end
