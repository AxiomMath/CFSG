module

public import Certificates.Kernel.L34W.D
public import Certificates.Data.Kernel.L34W.Types

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem kc_k0 : kcR kbMasks 0 16384 = true := by decide +kernel

theorem kc_k1 : kcR kbMasks 16384 16384 = true := by decide +kernel

theorem kc_k2 : kcR kbMasks 32768 16384 = true := by decide +kernel

theorem kc_k3 : kcR kbMasks 49152 16384 = true := by decide +kernel

theorem cj_k : cjOK GT YT outerTypes = true := by decide +kernel

theorem to_k : toOK TY = true := by decide +kernel

theorem tp_k : tpOK OT CM TY = true := by decide +kernel

theorem fs_k : fsOK T1X.F AlX.F OT BT TY = true := by decide +kernel

end CertificateChecks.KernelL34W

end
