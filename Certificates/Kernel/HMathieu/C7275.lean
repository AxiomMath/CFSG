module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Data.ASVolIK42

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C7275

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem coc : gAllR 191 (fun st y => T24.Mc.getD y [] :: st)
    (fun _ _ st => noQuadRank3 11 actM st) 6 [] [191] (2 ^ 191 - 1) [] T24.rows 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem code : gAllR 191 (fun st y => T24.Md.getD y [] :: st)
    (fun _ _ st => noQuadRank3 11 actM st) 6 [] [191] (2 ^ 191 - 1) [] T24.rows 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C7275

end
