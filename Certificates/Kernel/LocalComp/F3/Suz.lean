module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CFSGNative.Filter.SuzData
public import Certificates.Data.WCSporRot
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.F3.Suz 3 64
  CFSG.Blueprint.NativeSporadic.SuzSeed1 CFSG.Blueprint.NativeSporadic.SuzSeed2

public section

namespace CFSG.KD.LC.F3.Suz

open CFSG.KC.OpsLayK CFSG.SectionRank.Native

theorem sec_K : secK lay A B suzSec = true := by decide +kernel

theorem mult_K : sqK lay A B suzMultData = true := by decide +kernel

theorem rot_K : sqK lay A B suzFiveRot = true := by decide +kernel

theorem sec_neg_seeds : (!secK lay B A suzSec) = true := by decide +kernel

theorem mult_neg : (!sqK lay A B { suzMultData with a := suzMultData.a + 1 }) = true := by
  decide +kernel

theorem rot_neg : (!sqK lay A B { suzFiveRot with oh := suzFiveRot.oh + 1 }) = true := by
  decide +kernel

end CFSG.KD.LC.F3.Suz

end
