module

public import Certificates.Kernel.OmegaEight.SB3872L
public import Certificates.Kernel.OmegaEight.SB3872F
public import Certificates.Kernel.OmegaEight.SB3872KC
public import Certificates.Kernel.OmegaEight.SB3872Z01
public import Certificates.Kernel.OmegaEight.SB3872Z23
public import Certificates.Kernel.OmegaEight.SB3872Z45
public import Certificates.Kernel.OmegaEight.SB3872Z67

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem zOK_all : ∀ k < 8, zOK k = true := by
  intro k hk
  interval_cases k
  exacts [zOK_0, zOK_1, zOK_2, zOK_3, zOK_4, zOK_5, zOK_6, zOK_7]

set_option maxHeartbeats 0 in
theorem cands_check :
    (t1Cands.all fun c => t1List.any fun d => d.1 == c.1 && d.2.1 == c.2.1 && d.2.2.1 == c.2.2) =
      true := by
  rw [t1Cands_eq zOK_all]
  decide +kernel

theorem enum_check : t1EnumCheck = true := by
  unfold t1EnumCheck
  rw [leaves_check, fixmap_check, cands_check, kill_check]
  rfl

end CertificateChecks.KernelO8.SB3872

end
