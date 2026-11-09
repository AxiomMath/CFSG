module

public import Certificates.Kernel.ThCent.LDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs
public import CFSG.Certificates.Kernel.ThCent.DistSort

public section

namespace CFSG.KD.ThCent.L

theorem dist5_ok : dist5 = true := by
  rw [dist5]
  exact CFSG.KC.ThCent.distinctL_of_nodup _ (CFSG.KS.F3152.nodup_of_sortedK (by quickRfl))

end CFSG.KD.ThCent.L

end
