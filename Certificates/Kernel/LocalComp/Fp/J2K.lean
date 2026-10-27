module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Kernel.LocalComp.Fp.J2Data
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.Fp.J2K 5 14
  CFSG.Blueprint.NativeSporadic.J2Seed1 CFSG.Blueprint.NativeSporadic.J2Seed2

public section

namespace CFSG.KD.LC.Fp.J2K

open CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.KD.LC.Fp.J2D

theorem sec_K : secK lay A B j2SecK = true := by decide +kernel

theorem sec_neg_seeds : (!secK lay B A j2SecK) = true := by decide +kernel

end CFSG.KD.LC.Fp.J2K

end
