module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.Route
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vW0
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vW1
public import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vW2
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XGRuE2.All
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK000
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK001
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK002
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK003
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK004
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK005
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK006
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK007
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK008
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK009
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK010
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK011
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK012
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK013
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK014
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK015
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK016
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK017
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK018
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK019
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK020
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK021
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK022
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK023
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK024
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK025
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK026
import CFSG.Certificates.Kernel.Bounds.XGRuE2.T1vK027

public section

#kb_cert CFSG.KBRoute.XGRuE2 T1 XGRuE2_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XGRuE2/data/XGRuE2_T1v.meta" 166702 706066429356552441 CFSG.KBRoute.XGRuE2.rels

namespace CertificateChecks.KernelMiscCoset.XGRuE2

theorem t1 : CFSG.KBRoute.XGRuE2.T1.ok = true := by kb_assemble XGRuE2_T1v

end CertificateChecks.KernelMiscCoset.XGRuE2

end
