module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Data.Kernel.HMathieu.PredKS
public import Certificates.Data.Kernel.HMathieu.Orb

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C7260

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU24
open CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem search : gAllR 191 (fun st y => (T24.Md.getD y [] :: st.1,
      st.2.filter fun m => actM (T24.Md.getD y []) m == m)) (fun _ _ st => predKSK st) 6 [] [191]
    (2 ^ 191 - 1) ([], List.range (2 ^ 11)) T24.rows 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem orbS : orbCount [codColsA, codColsB] uSBasis 1771 = 1771 := by decide +kernel

set_option maxHeartbeats 0 in
theorem orbT : orbCount [cocColsA, cocColsB] uTBasis' 3795 = 3795 := by decide +kernel

end CertificateChecks.KernelHMathieu.C7260

end
