module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import Certificates.Kernel.HeMult.P3Data
public import Certificates.Kernel.HeMult.P2Data
public import Certificates.Kernel.HeMult.P1Data
public import Certificates.Kernel.HeMult.C3Data
public import Certificates.Kernel.HeMult.C2Data
public import Certificates.Kernel.HeMult.C1Data
public import Certificates.Kernel.HeMult.Words
import CFSG.Certificates.Kernel.Bounds.Load
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

open CFSG.Certificates

public section

namespace CFSG.KBRoute.HeMP3

#kb_table CFSG.KBRoute.HeMP3 T1 HeMP3_T1v include_bytes "data/HeMP3_T1v.meta" 48546 17346307315279397220 67305985 CertificateChecks.KernelHeMult.rels4 "1 2 3"

theorem top : KB.topOk T1.amap (nat_lit 4) = true := by quickRfl

end CFSG.KBRoute.HeMP3

namespace CFSG.KBRoute.HeMP2

#kb_table CFSG.KBRoute.HeMP2 T1 HeMP2_T1v include_bytes "data/HeMP2_T1v.meta" 298 17013601558386885033 197121 CertificateChecks.KernelHeMult.rels3 "1 2"

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.HeMP2

namespace CFSG.KBRoute.HeMP1

#kb_table CFSG.KBRoute.HeMP1 T1 HeMP1_T1v include_bytes "data/HeMP1_T1v.meta" 1466 7090410320137924932 513 CertificateChecks.KernelHeMult.rels2 ""

theorem top : KB.topOk T1.amap (nat_lit 2) = true := by quickRfl

end CFSG.KBRoute.HeMP1

namespace CFSG.KBRoute.HeMC3

#kb_table CFSG.KBRoute.HeMC3 T1 HeMC3_T1v include_bytes "data/HeMC3_T1v.meta" 273139 7968643691758189446 67305985 CertificateChecks.KernelHeMult.cover4 "1 2 3"

theorem top : KB.topOk T1.amap (nat_lit 4) = true := by quickRfl

end CFSG.KBRoute.HeMC3

namespace CFSG.KBRoute.HeMC2

#kb_table CFSG.KBRoute.HeMC2 T1 HeMC2_T1v include_bytes "data/HeMC2_T1v.meta" 5804 4937013977989397675 197121 CertificateChecks.KernelHeMult.cover3 "1 2"

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.HeMC2

namespace CFSG.KBRoute.HeMC1

#kb_table CFSG.KBRoute.HeMC1 T1 HeMC1_T1v include_bytes "data/HeMC1_T1v.meta" 4309 4029380975679089947 513 CertificateChecks.KernelHeMult.cover2 ""

theorem top : KB.topOk T1.amap (nat_lit 2) = true := by quickRfl

end CFSG.KBRoute.HeMC1

end
