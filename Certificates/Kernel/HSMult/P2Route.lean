module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import Certificates.Kernel.HSMult.P2Data
public import Certificates.Kernel.HSMult.Words
import CFSG.Certificates.Kernel.Bounds.Load
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

open CFSG.Certificates

public section

namespace CFSG.KBRoute.HSMP2

#kb_table CFSG.KBRoute.HSMP2 T1 HSMP2_T1v include_bytes "data/HSMP2_T1v.meta" 10434 16526001543835221162 6618611909121 CertificateChecks.KernelHSMult.rels6 "1 2 3 4 5"

theorem top : KB.topOk T1.amap (nat_lit 6) = true := by quickRfl

end CFSG.KBRoute.HSMP2

end
