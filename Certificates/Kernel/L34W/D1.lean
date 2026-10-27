module

public import Certificates.Kernel.L34W.Outer
public import Certificates.Data.Kernel.L34W.Fix
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.L34W.D1Data

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelL34W.D1W CertificateChecks.KernelL34W.d1Arr 10

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

@[expose] noncomputable def d1OK (lo n : Nat) : Bool :=
  allN n fun q => d1One T1X.F AlX.F OT BT CM D1W (kbMasks.getD (Nat.add lo q) 0) (Nat.add lo q)

theorem d1_k0 : d1OK 0 5 = true := by decide +kernel

theorem d1_k5 : d1OK 5 5 = true := by decide +kernel

theorem d1_k10 : d1OK 10 4 = true := by decide +kernel

theorem d1_neg : (!d1One T1X.F AlX.F OT BT CM
    (patchT D1W 1872 (Nat.lor (Nat.sub (D1W 1872) (Nat.shiftLeft (pg 10 (mask 10) (D1W 1872) 1) 10))
      (Nat.shiftLeft (pg 10 (mask 10) (D1W 1872) 0) 10))) (kbMasks.getD 13 0) 13) = true := by
  decide +kernel

end CertificateChecks.KernelL34W

end
