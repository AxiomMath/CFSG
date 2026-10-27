module

public import Certificates.Kernel.B3S3.GenSl
public import Certificates.Kernel.Om1K.KeyPts
meta import Certificates.Kernel.Om1K.KeyPts
meta import Certificates.Data.Holder1711.Om1Check
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import CFSG.RankThree.Native.PermEnumeration

namespace CertificateChecks.KernelOm1

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data

meta def gS0 : Array (Array Nat) := wsA (reflTab ()) wS0

end CertificateChecks.KernelOm1

set_option maxRecDepth 400000

#kb3_enum_sl CertificateChecks.KernelOm1.E0 CertificateChecks.KernelOm1.gS0
  CertificateChecks.KernelOm1.keyPtsA 240 8 64
