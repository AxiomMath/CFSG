module

public import Certificates.Kernel.HMathieu.FixTab12
public import Certificates.Data.Kernel.HMathieu.PredXi

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C7113

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem search : gAllR 35 (fun st y => (T12.Mc.getD y [] :: st.1, if st.1.isEmpty then
      FixTab12.F12.getD y [] else st.2.filter fun m => actK (T12.Mc.getD y []) m == m))
    (predXiK 10 8 3 FixTab12.F12 35) 5 [] [35] (2 ^ 35 - 1) ([], List.range (2 ^ 10)) T12.rows 0 =
    true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C7113

end
