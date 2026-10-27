module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CFSGNative.Filter.HeData
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.Fp.He 7 50
  CFSG.Blueprint.NativeSporadic.HeSeed1 CFSG.Blueprint.NativeSporadic.HeSeed2

public section

namespace CFSG.KD.LC.Fp.He

open CFSG.KC.OpsLayK CFSG.SectionRank.Native

theorem sec_K : secK lay A B heSec = true := by decide +kernel

theorem sec_neg_seeds : (!secK lay B A heSec) = true := by decide +kernel

end CFSG.KD.LC.Fp.He

end
