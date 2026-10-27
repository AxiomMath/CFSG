module

public import Certificates.Kernel.HMathieu.T22
public import Certificates.Data.Kernel.HMathieu.PredHF

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C7225

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem search : gAllR 71 (fun st y => (T22.Md.getD y [] :: st.1,
      st.2.filter fun m => actM (T22.Md.getD y []) m == m)) (predHF22K T22.E T22.P) 5 [] [71]
    (2 ^ 71 - 1) ([], List.range (2 ^ 10)) T22.rows 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C7225

end
