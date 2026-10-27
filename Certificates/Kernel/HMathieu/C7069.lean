module

public import Certificates.Kernel.HMathieu.FixTab22
public import Certificates.Data.Kernel.HMathieu.PickE

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C7069

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem search : gAllR 71 (fun st y => (T22.Mc.getD y [] :: st.1, if st.1.isEmpty then
      FixTab22.F22.getD y [] else st.2.filter fun m => actK (T22.Mc.getD y []) m == m))
    (fun L S st => pred22E 9 T22.Mc FixTab22.F22 71 L S st && predOffK T22.P L S st) 6 [] [71]
    (2 ^ 71 - 1) ([], List.range (2 ^ 10)) T22.rows 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C7069

end
