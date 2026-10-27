module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import Certificates.Kernel.HSMult.C2Data
public import Certificates.Kernel.HSMult.Words
import CFSG.Certificates.Kernel.Bounds.Load
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

open CFSG.Certificates

public section

namespace CFSG.KBRoute.HSMC2

#kb_table CFSG.KBRoute.HSMC2 T1 HSMC2_T1v include_bytes "data/HSMC2_T1v.meta" 40411 9787343173744834628 6618611909121 CertificateChecks.KernelHSMult.cover6 "1 2 3 4 5"

theorem top : KB.topOk T1.amap (nat_lit 6) = true := by quickRfl

end CFSG.KBRoute.HSMC2

end
