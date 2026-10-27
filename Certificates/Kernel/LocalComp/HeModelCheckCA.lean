module

public import Certificates.Kernel.LocalComp.HeModelCheckDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.HexaKSound

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeModelCheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.HeModelK CFSG.KC.Enum CFSG.KS
open CFSG.KS.Prim CFSG.KS.Raw CertificateChecks.KernelLC
open CertificateChecks.KernelLC.BindL CertificateChecks.KernelLC.HeModel

theorem ca0 : allR (cAt d32) 0 2688 = true := by quickRfl
theorem ca1 : allR (cAt d32) 2688 2688 = true := by quickRfl
theorem ca2 : allR (cAt d32) 5376 2688 = true := by quickRfl
theorem ca3 : allR (cAt d32) 8064 2688 = true := by quickRfl
theorem ca4 : allR (cAt d32) 10752 2688 = true := by quickRfl
theorem ca5 : allR (cAt d32) 13440 2688 = true := by quickRfl
theorem ca6 : allR (cAt d32) 16128 2688 = true := by quickRfl
theorem ca7 : allR (cAt d32) 18816 2688 = true := by quickRfl

theorem caAll : allR (cAt d32) 0 (2688 * 8) = true :=
  allR_blocks (cAt d32) 2688 8 (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
    (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ forall_lt_zero ca0) ca1) ca2)
    ca3) ca4) ca5) ca6) ca7)

end CertificateChecks.KernelLC.HeModelCheck

end
