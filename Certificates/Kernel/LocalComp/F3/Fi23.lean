module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CFSGNative.Filter.Fi23Data
public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.F3.Fi23 3 253
  CFSG.Blueprint.NativeSporadic.Fi23Seed1 CFSG.Blueprint.NativeSporadic.Fi23Seed2

public section

namespace CFSG.KD.LC.F3.Fi23

open CFSG.KC.OpsLayK CFSG.SectionRank.Native

theorem sec_K : secK lay A B fi23Sec = true := by decide +kernel

theorem five_K : sqK lay A B (fi23MultFive ()) = true := by decide +kernel

theorem sec_neg_seeds : (!secK lay B A fi23Sec) = true := by decide +kernel

theorem five_neg : (!sqK lay A B { fi23MultFive () with r := 7 }) = true := by decide +kernel

end CFSG.KD.LC.F3.Fi23

end
