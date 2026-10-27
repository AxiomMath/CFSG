module

public import Certificates.Kernel.SporSch.Co2S.GenRebase
public import Certificates.Data.Kernel.SporSch.Co2SFix
public meta import Certificates.Data.Kernel.SporSch.Co2SFix
public import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import Std.Data.HashMap

set_option maxRecDepth 400000

#kss_rebase CertificateChecks.KernelSporSch.Co2ItC 2300 12 64 CFSG.Sporadic.Co2Schreier.aArrs
  CFSG.KS.SporSch.Co2SFix.co2ItBase 42305421312000 1 4
