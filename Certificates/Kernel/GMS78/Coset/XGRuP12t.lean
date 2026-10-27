module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XGRuP12t.Route
public import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vW0
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.All
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK000
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK001
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK002
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK003
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK004
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK005
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK006
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK007
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK008
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK009
import CFSG.Certificates.Kernel.Bounds.XGRuP12t.T1vK010

public section

#kb_cert CFSG.KBRoute.XGRuP12t T1 XGRuP12t_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XGRuP12t/data/XGRuP12t_T1v.meta" 61445 3472798169210265517 CFSG.KBRoute.XGRuP12t.rels

namespace CertificateChecks.KernelMiscCoset.XGRuP12t

theorem t1 : CFSG.KBRoute.XGRuP12t.T1.ok = true := by kb_assemble XGRuP12t_T1v

end CertificateChecks.KernelMiscCoset.XGRuP12t

end
