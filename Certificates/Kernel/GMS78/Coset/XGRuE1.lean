module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.Route
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vW2
public import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vW3
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XGRuE1.All
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK000
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK001
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK002
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK003
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK004
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK005
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK006
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK007
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK008
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK009
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK010
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK011
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK012
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK013
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK014
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK015
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK016
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK017
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK018
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK019
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK020
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK021
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK022
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK023
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK024
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK025
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK026
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK027
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK028
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK029
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK030
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK031
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK032
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK033
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK034
import CFSG.Certificates.Kernel.Bounds.XGRuE1.T1vK035

public section

#kb_cert CFSG.KBRoute.XGRuE1 T1 XGRuE1_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XGRuE1/data/XGRuE1_T1v.meta" 211743 3888154857150819772 CFSG.KBRoute.XGRuE1.rels

namespace CertificateChecks.KernelMiscCoset.XGRuE1

theorem t1 : CFSG.KBRoute.XGRuE1.T1.ok = true := by kb_assemble XGRuE1_T1v

end CertificateChecks.KernelMiscCoset.XGRuE1

end
