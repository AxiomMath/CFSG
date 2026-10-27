module

public import Certificates.Kernel.H13.O3Tac

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem o3_sub_om3 : subB o3G om3E = true := by
  rw [om3E]
  o3_sub_tac

set_option maxHeartbeats 0 in
theorem o3_sub_om3F : subB (o3G ++ [fG]) om3FE = true := by
  rw [om3FE]
  o3_sub_tac

set_option maxHeartbeats 0 in
theorem o3_sub_omN : subB (o3G ++ [fG, sG]) omNE = true := by
  rw [omNE]
  o3_sub_tac

set_option maxHeartbeats 0 in
theorem o3_sub_h1 : subB (o3G ++ [sG]) h1E = true := by
  rw [h1E]
  o3_sub_tac

set_option maxHeartbeats 0 in
theorem o3_sub_h2 : subB (o3G ++ [sfG]) h2E = true := by
  rw [h2E]
  o3_sub_tac

end CertificateChecks.KernelH13

end
