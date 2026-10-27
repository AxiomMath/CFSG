module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CFSGNative.MultRes.Witnesses
public import Certificates.Data.KFCub2McL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubData
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.F3.McL 3 21
  CFSG.Blueprint.NativeSporadic.McLSeed1 CFSG.Blueprint.NativeSporadic.McLSeed2

public section

namespace CFSG.KD.LC.F3.McL

open CFSG.KC.OpsLayK CFSG.SectionRank.Native

theorem mult_K : cubK lay A B mclMultData = true := by decide +kernel

theorem five_K : cub2K lay A B mclFiveData = true := by decide +kernel

theorem sylow5H_K : cubK lay A B CFSG.AGLEmbedding.SporCubic.mclSylow5HData = true := by
  decide +kernel

theorem mult_neg_seeds : (!cubK lay B A mclMultData) = true := by decide +kernel

theorem five_neg : (!cub2K lay A B { mclFiveData with
    h2 := { mclFiveData.h2 with oh := mclFiveData.h2.oh + 1 } }) = true := by
  decide +kernel

end CFSG.KD.LC.F3.McL

end
