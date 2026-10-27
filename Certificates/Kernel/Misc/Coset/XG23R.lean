module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.XG23R.Route
public import CFSG.Certificates.Kernel.Bounds.XG23R.T1vC0
public import CFSG.Certificates.Kernel.Bounds.XG23R.T1vC1
public import CFSG.Certificates.Kernel.Bounds.XG23R.T1vW0
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.XG23R.All
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK000
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK001
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK002
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK003
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK004
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK005
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK006
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK007
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK008
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK009
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK010
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK011
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK012
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK013
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK014
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK015
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK016
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK017
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK018
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK019
import CFSG.Certificates.Kernel.Bounds.XG23R.T1vK020

public section

#kb_cert CFSG.KBRoute.XG23R T1 XG23R_T1v include_bytes "../../../../CFSG/Certificates/Kernel/Bounds/XG23R/data/XG23R_T1v.meta" 120408 1930638362444289591 CFSG.KBRoute.XG23R.rels

namespace CertificateChecks.KernelMiscCoset.XG23R

theorem t1 : CFSG.KBRoute.XG23R.T1.ok = true := by kb_assemble XG23R_T1v

end CertificateChecks.KernelMiscCoset.XG23R

end
