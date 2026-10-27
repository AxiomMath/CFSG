module

public import Certificates.Kernel.HMathieu.T23C
public import Certificates.Kernel.HMathieu.T23X
public import Certificates.Data.Kernel.HMathieu.PickE

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C7072

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem search : gAllR 35 (fun st y => (T23C.Mc.getD y [] :: st.1, if st.1.isEmpty then
      T23C.F23c.getD y [] else st.2.filter fun m => actK (T23C.Mc.getD y []) m == m))
    (pred23K 4) 5 [] [35] (2 ^ 35 - 1) ([], List.range (2 ^ 11)) T23X.rows 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C7072

end
