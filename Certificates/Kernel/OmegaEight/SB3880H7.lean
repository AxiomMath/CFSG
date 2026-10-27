module

public import Certificates.Kernel.OmegaEight.SB3880CK
public import Certificates.Kernel.OmegaEight.SB3880D7
public import Certificates.Kernel.OmegaEight.SB3884V7
public import Certificates.Kernel.OmegaEight.SB3880V

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

namespace H7

theorem hmul : t1Mul (s2F 7) (s2Z 7) = MK 1 31 24 := by
  rw [s2F_eq (k := 1) (m := 31) rfl rfl]
  exact t1Mul_eq 24 V7.hw V7.hl

theorem blocks : ∀ s < 16, (List.range' (64 * s) 64).all (maskK (MK 1 31 24) vecK rw7
    (invRows63.flatten.map vecK)) = true := by
  intro s hs
  interval_cases s <;> decide +kernel

end H7

theorem char7 : l2eCharOK 7 (t1Vec vSArr) rw7 (invRows63.flatten.map vecK) = true :=
  l2eCharOK_of H7.hmul vec_get (by decide +kernel) (by rw [V7.hI])
    (all_range_blocks (B := 64) (n := 16) H7.blocks)

end CertificateChecks.KernelO8.SB3880

end
