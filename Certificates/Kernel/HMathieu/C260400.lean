module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Kernel.HMathieu.T22
public import Certificates.Kernel.HMathieu.T12
public import Certificates.Data.SmithB45MatQ

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C260400

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem coc24 : gAllR 191 (fun st y => T24.Mc.getD y [] :: st)
    (fun _ _ st => predQ 11 actM true st) 6 [] [191] (2 ^ 191 - 1) [] T24.rows 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem code24 : gAllR 191 (fun st y => T24.Md.getD y [] :: st)
    (fun _ _ st => predQ 11 actM true st) 6 [] [191] (2 ^ 191 - 1) [] T24.rows 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem coc22 : gAllR 71 (fun st y => T22.Mc.getD y [] :: st)
    (fun _ _ st => predQ 10 actM true st) 5 [] [71] (2 ^ 71 - 1) [] T22.rows 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem code22 : gAllR 71 (fun st y => T22.Md.getD y [] :: st)
    (fun _ _ st => predQ 10 actM false st) 5 [] [71] (2 ^ 71 - 1) [] T22.rows 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w12 : gAllR 35 (fun st y => T12.Mc.getD y [] :: st)
    (fun _ _ st => predQ 10 actM true st) 4 [] [35] (2 ^ 35 - 1) [] T12.rows 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C260400

end
