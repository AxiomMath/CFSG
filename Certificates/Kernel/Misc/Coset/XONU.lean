module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XONU.Route
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW2
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW3
public import CFSG.Certificates.Kernel.Bounds.XONU.T1vW4
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XONU.All
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK000
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK001
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK002
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK003
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK004
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK005
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK006
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK007
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK008
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK009
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK010
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK011
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK012
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK013
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK014
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK015
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK016
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK017
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK018
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK019
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK020
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK021
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK022
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK023
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK024
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK025
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK026
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK027
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK028
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK029
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK030
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK031
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK032
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK033
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK034
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK035
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK036
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK037
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK038
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK039
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK040
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK041
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK042
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK043
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK044
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK045
import CFSG.Certificates.Kernel.Bounds.XONU.T1vK046

public section

#kb_cert CFSG.KBRoute.XONU T1 XONU_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XONU/data/XONU_T1v.meta" 276484 16117330287017658704 CFSG.KBRoute.XONU.rels

namespace CertificateChecks.KernelMiscCoset.XONU

theorem t1 : CFSG.KBRoute.XONU.T1.ok = true := by kb_assemble XONU_T1v

end CertificateChecks.KernelMiscCoset.XONU

end
