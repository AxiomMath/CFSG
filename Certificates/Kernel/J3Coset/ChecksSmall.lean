module

public import Certificates.Kernel.J3Coset.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3C

open CFSG.KD.J3C

theorem fix_ok : fixChk = true := by quickRfl

theorem q_ok : qChk = true := by quickRfl

theorem o_ok : oChk = true := by quickRfl

theorem ld_ok : ldChk = true := by quickRfl

theorem cov_ok : covChk = true := by quickRfl

theorem out_ok : outChk = true := by quickRfl

@[expose] noncomputable def idxChk : Bool :=
  zc.all (· < 9) && zk.all (· < 9) && Oc.length == 31 && !(beta0 == 0)

theorem idx_ok : idxChk = true := by quickRfl

@[expose] noncomputable def yChk : Bool := Oc.flatten.all fun r => r.2.2.2.1 < 25840

theorem y_ok : yChk = true := by quickRfl

end CertificateChecks.KernelJ3C

end
