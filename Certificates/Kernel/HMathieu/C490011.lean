module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Data.Kernel.HMathieu.PredMisc

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C490011

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem search : gAllR 191 (fun st y => (T24.Mc.getD y [] :: st.1,
      st.2.filter fun m => actM (T24.Mc.getD y []) m == m)) (fun L _ st => predOff24K T24.P L st) 7
    [] [191] (2 ^ 191 - 1) ([], List.range (2 ^ 11)) T24.rows 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C490011

end
