module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayK
public import CFSG.GH74.Generic.NativeCertsInputs
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.Fp.Ly 5 111
  CFSG.Blueprint.NativeSporadic.LySeed1 CFSG.Blueprint.NativeSporadic.LySeed2

public section

namespace CFSG.KD.LC.Fp.Ly

open CFSG.KC.OpsLayK CFSG.SectionRank.Native

theorem sec_K : secK lay A B CFSG.GH74.Generic.lySec = true := by decide +kernel

theorem sec_neg_seeds : (!secK lay B A CFSG.GH74.Generic.lySec) = true := by decide +kernel

end CFSG.KD.LC.Fp.Ly

end
