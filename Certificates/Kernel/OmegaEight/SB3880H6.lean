module

public import Certificates.Kernel.OmegaEight.SB3880CK
public import Certificates.Kernel.OmegaEight.SB3880D6
public import Certificates.Kernel.OmegaEight.SB3884V6
public import Certificates.Kernel.OmegaEight.SB3880V

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

namespace H6

theorem hmul : t1Mul (s2F 6) (s2Z 6) = MK 1 26 24 := by
  rw [s2F_eq (k := 1) (m := 26) rfl rfl]
  exact t1Mul_eq 24 V6.hw V6.hl

theorem blocks : ∀ s < 16, (List.range' (64 * s) 64).all (maskK (MK 1 26 24) vecK rw6
    (invRows53.flatten.map vecK)) = true := by
  intro s hs
  interval_cases s <;> decide +kernel

end H6

theorem char6 : l2eCharOK 6 (t1Vec vSArr) rw6 (invRows53.flatten.map vecK) = true :=
  l2eCharOK_of H6.hmul vec_get (by decide +kernel) (by rw [V6.hI])
    (all_range_blocks (B := 64) (n := 16) H6.blocks)

end CertificateChecks.KernelO8.SB3880

end
