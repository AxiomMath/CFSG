module

public import Certificates.Kernel.LocalComp.HeldFixGraph.C0
public import Certificates.Kernel.LocalComp.HeldFixGraph.C1
public import Certificates.Kernel.LocalComp.HeldFixGraph.C2
public import Certificates.Kernel.LocalComp.HeldFixGraph.C3
import Certificates.Kernel.LocalQT.Tc.Gen

public section

set_option maxRecDepth 400000

#kqb_all CertificateChecks.KernelLC.HFG CertificateChecks.KernelLC.HeldFixGraph.ck 630

end
