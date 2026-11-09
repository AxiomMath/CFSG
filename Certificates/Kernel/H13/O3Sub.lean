module

public import Certificates.Kernel.H13.O3Tac
public import Certificates.Kernel.H13.BfsO3

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.KC.Mat8P CFSG.KC.Mat8T

set_option maxRecDepth 100000

theorem o3_sub_om3 : subB o3G om3E = true := by
  rw [om3E]
  exact subB_of_bfs _ (by decide) _ bfsOm3_bfs (by decide +kernel)

theorem o3_sub_om3F : subB (o3G ++ [fG]) om3FE = true := by
  rw [om3FE]
  exact subB_of_bfs _ (by decide) _ bfsOm3F_bfs (by decide +kernel)

theorem o3_sub_omN : subB (o3G ++ [fG, sG]) omNE = true := by
  rw [omNE]
  exact subB_of_bfs _ (by decide) _ bfsOmN_bfs (by decide +kernel)

theorem o3_sub_h1 : subB (o3G ++ [sG]) h1E = true := by
  rw [h1E]
  exact subB_of_bfs _ (by decide) _ bfsH1_bfs (by decide +kernel)

theorem o3_sub_h2 : subB (o3G ++ [sfG]) h2E = true := by
  rw [h2E]
  exact subB_of_bfs _ (by decide) _ bfsH2_bfs (by decide +kernel)

end CertificateChecks.KernelH13

end
