module

public import Certificates.Kernel.HMathieu.T22
public import Certificates.Data.Kernel.HMathieu.PredMisc

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C7240

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem search : gAllR 71 (fun st y => T22.Md.getD y [] :: st)
    (fun L _ Ms => predQ22inK T22.P L Ms) 5 [] [71] (2 ^ 71 - 1) [] T22.rows 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C7240

end
