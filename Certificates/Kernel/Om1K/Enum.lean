module

public import Certificates.Kernel.Om1K.EnumS0
public import Certificates.Kernel.Om1K.EnumSa
public import Certificates.Kernel.Om1K.Defs
meta import Certificates.Kernel.Om1K.KeyPts
meta import Certificates.Kernel.Om1K.Defs
meta import Certificates.Data.Holder1711.Om1Check
public import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.SetOrb
meta import Certificates.Data.Holder1711.Om2Check
meta import Certificates.Data.Kernel.SetOrb

namespace CertificateChecks.KernelOm1

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data

meta def gP3 : Array (Array Nat) := wsA (reflTab ()) wP3
meta def gPa3 : Array (Array Nat) := wsA (reflTab ()) wPa3
meta def gPa5 : Array (Array Nat) := wsA (reflTab ()) wPa5
meta def gSc : Array (Array Nat) := wsA (reflTab ()) wSc
meta def gPc : Array (Array Nat) := wsA (reflTab ()) wPc
meta def gK0 : Array (Array Nat) := wsA (reflTab ()) A.k0W

end CertificateChecks.KernelOm1

set_option maxRecDepth 400000

#kb3_enum_sl CertificateChecks.KernelOm1.E1 CertificateChecks.KernelOm1.gP3
  CertificateChecks.KernelOm1.keyPtsA 240 8 27
#kb3_enum_sl CertificateChecks.KernelOm1.Ea3 CertificateChecks.KernelOm1.gPa3
  CertificateChecks.KernelOm1.keyPtsA 240 8 9
#kb3_enum_sl CertificateChecks.KernelOm1.Ea5 CertificateChecks.KernelOm1.gPa5
  CertificateChecks.KernelOm1.keyPtsA 240 8 5
#kb3_enum_sl CertificateChecks.KernelOm1.Ec CertificateChecks.KernelOm1.gSc
  CertificateChecks.KernelOm1.keyPtsA 240 8 64
#kb3_enum_sl CertificateChecks.KernelOm1.Epc CertificateChecks.KernelOm1.gPc
  CertificateChecks.KernelOm1.keyPtsA 240 8 3
#kb3_enum_sl CertificateChecks.KernelOm1.EK CertificateChecks.KernelOm1.gK0
  CertificateChecks.KernelOm1.keyPtsA 240 8 32
