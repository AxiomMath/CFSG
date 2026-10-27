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

theorem ub0 : allR UB 0 128 = true := by quickRfl
theorem ub1 : allR UB 128 128 = true := by quickRfl
theorem ub2 : allR UB 256 128 = true := by quickRfl
theorem ub3 : allR UB 384 128 = true := by quickRfl
theorem ub4 : allR UB 512 128 = true := by quickRfl
theorem ub5 : allR UB 640 128 = true := by quickRfl
theorem ub6 : allR UB 768 128 = true := by quickRfl
theorem ub7 : allR UB 896 128 = true := by quickRfl

theorem uc0 : allR UBC 0 256 = true := by quickRfl
theorem uc1 : allR UBC 256 256 = true := by quickRfl
theorem uc2 : allR UBC 512 256 = true := by quickRfl
theorem uc3 : allR UBC 768 256 = true := by quickRfl

theorem ubAll : allR UB 0 (128 * 8) = true :=
  allR_blocks UB 128 8 (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
    (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ forall_lt_zero ub0) ub1) ub2)
    ub3) ub4) ub5) ub6) ub7)

theorem ucAll : allR UBC 0 (256 * 4) = true :=
  allR_blocks UBC 256 4 (forall_lt_succ (forall_lt_succ (forall_lt_succ (forall_lt_succ
    forall_lt_zero uc0) uc1) uc2) uc3)

end CertificateChecks.KernelLC.HeModelCheck

end
