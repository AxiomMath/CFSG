module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CFSGNative.Filter.HNData
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.Fp.HN 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2

public section

namespace CFSG.KD.LC.Fp.HN

open CFSG.KC.OpsLayK CFSG.SectionRank.Native

theorem sec_K : secK lay A B hnSec = true := by decide +kernel

theorem sec_neg_seeds : (!secK lay B A hnSec) = true := by decide +kernel

end CFSG.KD.LC.Fp.HN

end
