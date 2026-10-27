module

public import Certificates.Kernel.KGC31J2.Defs
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck
public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Data.Kernel.KGC31PGrid

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelKGC31J2.invBlk 12 15

end
