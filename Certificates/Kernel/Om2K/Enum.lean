module

public import Certificates.Kernel.B3S3.GenSl
public import Certificates.Kernel.Om2K.Defs
public import Certificates.Kernel.Om2K.KeyPts
meta import Certificates.Kernel.Om2K.KeyPts
meta import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.SetOrb

namespace CertificateChecks.KernelOm2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab)

meta def gensOf (ws : List (List Nat)) : Array (Array Nat) := (ws.map (wY (lettersY (reflTab ())))).toArray

meta def gS0 : Array (Array Nat) := gensOf wS0
meta def gP3 : Array (Array Nat) := gensOf wP3
meta def gSc : Array (Array Nat) := gensOf wSc
meta def gPc : Array (Array Nat) := gensOf wPc
meta def gCR : Array (Array Nat) := gensOf wCR

end CertificateChecks.KernelOm2

set_option maxRecDepth 400000

#kb3_enum_sl CertificateChecks.KernelOm2.E0 CertificateChecks.KernelOm2.gS0
  CertificateChecks.KernelOm2.keyPtsYA 480 9 64
#kb3_enum_sl CertificateChecks.KernelOm2.E1 CertificateChecks.KernelOm2.gP3
  CertificateChecks.KernelOm2.keyPtsYA 480 9 27
#kb3_enum_sl CertificateChecks.KernelOm2.E2 CertificateChecks.KernelOm2.gSc
  CertificateChecks.KernelOm2.keyPtsYA 480 9 64
#kb3_enum_sl CertificateChecks.KernelOm2.E3 CertificateChecks.KernelOm2.gPc
  CertificateChecks.KernelOm2.keyPtsYA 480 9 3
#kb3_enum_sl CertificateChecks.KernelOm2.E4 CertificateChecks.KernelOm2.gCR
  CertificateChecks.KernelOm2.keyPtsYA 480 9 64
