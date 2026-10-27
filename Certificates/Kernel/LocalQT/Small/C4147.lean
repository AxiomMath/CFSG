module

public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import Certificates.Certificate113

public section

namespace CFSG.KD.LQT.C4147

open CFSG.KC.LQT.S CFSG.QuasithinUnique.Id2519.HSAut

theorem hL : classSizes.toList =
    [1, 1260, 1344, 105, 1680, 3360, 1344, 2880, 2880, 112, 2520, 1344, 1120, 210] := by
  decide +kernel
theorem hk : classSizes.size = 14 := by decide +kernel
theorem hc : c4147 [1, 1260, 1344, 105, 1680, 3360, 1344, 2880, 2880, 112, 2520, 1344, 1120, 210]
    14 20160 = true := by quickRfl

end CFSG.KD.LQT.C4147

end
