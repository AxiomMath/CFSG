module

public import Certificates.Kernel.Fi22Cent.Defs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.PC CFSG.KS.Fi22Cent CertificateChecks.KernelFi22C

set_option Elab.async false

theorem ea_ok : eaK = true := by quickRfl
theorem ep_ok : epK = true := by quickRfl
theorem phi_ok : phiK = true := by quickRfl
theorem tree_ok : treeK = true := by quickRfl
theorem pow1_ok : powK [3468, 3243, 2605, 168, 1897] 9 QL = true := by quickRfl
theorem pow2_ok : powK [889, 1897, 2614, 929, 3173, 762] 11 QL = true := by quickRfl
theorem lv_len : Nat.beq (lvK LJ BJ 32 1).length 30 = true := by quickRfl
theorem phd_ok : CFSG.KS.T46K.eqLF PHK 0 (CFSG.Sporadic.Fi22.Native.phiData.toList) = true := by
  quickRfl

end CertificateChecks.KernelFi22Cent

#kon_slices CertificateChecks.KernelFi22Cent.rs 0 6
#kon_slices CertificateChecks.KernelFi22Cent.lvSl 0 30

end
