module

public import Certificates.Kernel.Om2K.CertGen
public import Certificates.Kernel.Om1K.Defs
meta import Certificates.Data.Holder1711.Om1Check
meta import Certificates.Kernel.Om1K.Defs
public import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.SetOrb
meta import Certificates.Data.Holder1711.Om2Check
meta import Certificates.Data.Kernel.BfsPin
meta import Certificates.Data.Kernel.SetOrb

namespace CertificateChecks.KernelOm1.A

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data

meta def imgsM (ws : List (List Nat)) : List (Array Nat) := ws.map (wA (reflTab ()))

meta def elM : List (Array Nat) := imgsM elW
meta def tgM : List (Array Nat) := imgsM wT
meta def caM : List (Array Nat) := imgsM wCa
meta def ccM : List (Array Nat) := imgsM wCc
meta def wsM : List (Array Nat) := imgsM wSub
meta def xgM : List (Array Nat) := imgsM wX
meta def xiM : List (Array Nat) := imgsM wXr

end CertificateChecks.KernelOm1.A

public section

set_option maxRecDepth 400000

#perm_tab CertificateChecks.KernelOm1.A.EL CertificateChecks.KernelOm1.A.elM 8
#perm_tab CertificateChecks.KernelOm1.A.TG CertificateChecks.KernelOm1.A.tgM 8
#perm_tab CertificateChecks.KernelOm1.A.CA CertificateChecks.KernelOm1.A.caM 8
#perm_tab CertificateChecks.KernelOm1.A.CC CertificateChecks.KernelOm1.A.ccM 8
#perm_tab CertificateChecks.KernelOm1.A.WS CertificateChecks.KernelOm1.A.wsM 8
#perm_tab CertificateChecks.KernelOm1.A.XG CertificateChecks.KernelOm1.A.xgM 8
#perm_tab CertificateChecks.KernelOm1.A.XI CertificateChecks.KernelOm1.A.xiM 8

end
