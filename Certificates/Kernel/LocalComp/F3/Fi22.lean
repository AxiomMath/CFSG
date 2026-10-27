module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CFSGNative.Filter.Fi22Data
public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.F3.Fi22 3 77
  CFSG.Blueprint.NativeSporadic.Fi22Seed1 CFSG.Blueprint.NativeSporadic.Fi22Seed2

public section

namespace CFSG.KD.LC.F3.Fi22

open CFSG.KC.OpsLayK CFSG.SectionRank.Native

theorem sec_K : secK lay A B fi22Sec = true := by decide +kernel

theorem five_K : sqK lay A B (fi22MultFive ()) = true := by decide +kernel

theorem sec_neg_seeds : (!secK lay B A fi22Sec) = true := by decide +kernel

theorem five_neg : (!sqK lay A B { fi22MultFive () with r := 7 }) = true := by decide +kernel

end CFSG.KD.LC.F3.Fi22

end
