module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CFSGNative.Filter.Fi23Data
public import Certificates.Data.CFSGNative.ComponentPrimary.Witnesses
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CFSG.KD.LC.F3.Fi23 3 253
  CFSG.Blueprint.NativeSporadic.Fi23Seed1 CFSG.Blueprint.NativeSporadic.Fi23Seed2
