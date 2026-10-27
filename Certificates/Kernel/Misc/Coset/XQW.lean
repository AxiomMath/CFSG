module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XQW.Route
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW2
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW3
public import CFSG.Certificates.Kernel.Bounds.XQW.T1vW4
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XQW.All
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK000
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK001
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK002
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK003
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK004
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK005
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK006
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK007
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK008
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK009
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK010
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK011
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK012
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK013
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK014
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK015
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK016
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK017
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK018
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK019
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK020
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK021
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK022
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK023
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK024
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK025
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK026
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK027
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK028
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK029
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK030
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK031
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK032
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK033
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK034
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK035
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK036
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK037
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK038
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK039
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK040
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK041
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK042
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK043
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK044
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK045
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK046
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK047
import CFSG.Certificates.Kernel.Bounds.XQW.T1vK048

public section

#kb_cert CFSG.KBRoute.XQW T1 XQW_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XQW/data/XQW_T1v.meta" 275056 5348060446428055382 CFSG.KBRoute.XQW.rels

namespace CertificateChecks.KernelMiscCoset.XQW

theorem t1 : CFSG.KBRoute.XQW.T1.ok = true := by kb_assemble XQW_T1v

end CertificateChecks.KernelMiscCoset.XQW

end
