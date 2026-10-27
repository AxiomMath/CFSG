module

public import Certificates.Kernel.Om2K.Defs
public meta import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Each
public import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.SetOrb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check

@[expose] noncomputable def wordOKc (c : Nat) : Bool :=
  allN 32 fun d => okK (wYK (allWordsY.getD (Nat.add (Nat.mul 32 c) d) []))

theorem kLen : allWordsY.length = 257 := by decide +kernel

theorem kLetters : allWordsY.all wordYOK = true := by decide +kernel

end CertificateChecks.KernelOm2

#kc_each CertificateChecks.KernelOm2.wordOKc 0 9

end
