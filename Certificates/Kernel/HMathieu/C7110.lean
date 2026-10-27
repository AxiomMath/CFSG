module

public import Certificates.Kernel.HMathieu.T23X
public import Certificates.Data.Kernel.HMathieu.PickK

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C7110

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem search : gAllR 35 (fun st y => (T23.Md.getD y [] :: st.1, if st.1.isEmpty then
      T23X.F23.getD y [] else st.2.filter fun m => actK (T23.Md.getD y []) m == m))
    (predXiKF 11 10 11 T23X.F23 35) 4 [] [35] (2 ^ 35 - 1) ([], List.range (2 ^ 11)) T23X.rows 0 =
    true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C7110

end
