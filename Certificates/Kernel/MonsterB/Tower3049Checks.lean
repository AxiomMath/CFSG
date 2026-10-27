module

public import Certificates.Kernel.MonsterB.Tower3049Data
public import Certificates.Data.Kernel.MonsterB.Tower
import CFSG.Certificates.Kernel.Common.Cover

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Tower3049

open CFSG.KC.Tower

theorem node_chk : ∀ j < 5282, nodeK DA DB Certificates.Tw3049T j = true := by
  kc_cover 256

theorem pt_chk0 : ∀ k < 2300, ptK V W Certificates.Tw3049T 0 1 [] k = true := by
  kc_cover 256

theorem pt_chk1 : ∀ k < 1408, ptK V W Certificates.Tw3049T 2300 1301533 [1] k = true := by
  kc_cover 256

theorem pt_chk2 : ∀ k < 840,
    ptK V W Certificates.Tw3049T 3708 3153062 [1, 1301533] k = true := by
  kc_cover 256

theorem pt_chk3 : ∀ k < 216,
    ptK V W Certificates.Tw3049T 4548 3001345 [1, 1301533, 3153062] k = true := by
  kc_cover 256

theorem pt_chk4 : ∀ k < 36,
    ptK V W Certificates.Tw3049T 4764 2523750 [1, 1301533, 3153062, 3001345] k = true := by
  kc_cover 256

theorem pt_chk5 : ∀ k < 2, ptK V W Certificates.Tw3049T 4800 466291
    [1, 1301533, 3153062, 3001345, 2523750] k = true := by
  kc_cover 256

theorem srt_chk0 : ∀ m < 2300, srtK V Certificates.Tw3049S0 0 2300 m = true := by
  kc_cover 256

theorem srt_chk1 : ∀ m < 1408, srtK V Certificates.Tw3049S1 2300 1408 m = true := by
  kc_cover 256

theorem srt_chk2 : ∀ m < 840, srtK V Certificates.Tw3049S2 3708 840 m = true := by
  kc_cover 256

theorem srt_chk3 : ∀ m < 216, srtK V Certificates.Tw3049S3 4548 216 m = true := by
  kc_cover 256

theorem srt_chk4 : ∀ m < 36, srtK V Certificates.Tw3049S4 4764 36 m = true := by
  kc_cover 256

theorem srt_chk5 : ∀ m < 2, srtK V Certificates.Tw3049S5 4800 2 m = true := by
  kc_cover 256

end CertificateChecks.Tower3049

end
