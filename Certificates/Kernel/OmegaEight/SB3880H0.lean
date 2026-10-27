module

public import Certificates.Kernel.OmegaEight.SB3880O00
public import Certificates.Kernel.OmegaEight.SB3880O01
public import Certificates.Kernel.OmegaEight.SB3880O02
public import Certificates.Kernel.OmegaEight.SB3880O03
public import Certificates.Kernel.OmegaEight.SB3880D0
public import Certificates.Kernel.OmegaEight.SB3880V
public import Certificates.Kernel.OmegaEight.SB3884V0

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

namespace H0

theorem hmul : t1Mul (s2F 0) (s2Z 0) = MK 0 16 0 := by
  rw [s2F_eq (k := 0) (m := 16) rfl rfl]
  exact t1Mul_eq 0 V0.hw V0.hl

theorem o4b (s : ℕ) (hs : s < 16) :
    o4c (MK 0 16 0) vecK 8 (List.range' (8192 * s) 8192) = o4Lit.getD s 0 := by
  rcases (by omega : s < 4 ∨ (4 ≤ s ∧ s < 8) ∨ (8 ≤ s ∧ s < 12) ∨ 12 ≤ s) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
  · exact o4b0_0 s (Nat.zero_le _) h
  · exact o4b0_1 s h1 h2
  · exact o4b0_2 s h1 h2
  · exact o4b0_3 s h hs

theorem mask8 : maskK (MK 0 16 0) vecK rw0 (invRows0.flatten.map vecK) 8 = true := by
  have hsum : ((List.range 16).map fun s => o4c (MK 0 16 0) vecK 8
      (List.range' (8192 * s) 8192)).sum = 45312 := by
    rw [List.map_congr_left fun s hs => o4b s (List.mem_range.1 hs)]
    rfl
  unfold maskK
  rw [o4c_blocks, hsum]
  decide +kernel

theorem block0 : (List.range' (64 * 0) 64).all (maskK (MK 0 16 0) vecK rw0
    (invRows0.flatten.map vecK)) = true := by
  have e : List.range' (64 * 0) 64 = List.range' 0 8 ++ 8 :: List.range' 9 55 := by decide
  rw [e, List.all_append, List.all_cons, mask8]
  have h1 : (List.range' 0 8).all (maskK (MK 0 16 0) vecK rw0 (invRows0.flatten.map vecK)) =
    true := by decide +kernel
  have h2 : (List.range' 9 55).all (maskK (MK 0 16 0) vecK rw0 (invRows0.flatten.map vecK)) =
    true := by decide +kernel
  rw [h1, h2]
  rfl

theorem blocks : ∀ s < 16, (List.range' (64 * s) 64).all (maskK (MK 0 16 0) vecK rw0
    (invRows0.flatten.map vecK)) = true := by
  intro s hs
  interval_cases s
  · exact block0
  all_goals decide +kernel

end H0

theorem char0 : l2eCharOK 0 (t1Vec vSArr) rw0 (invRows0.flatten.map vecK) = true :=
  l2eCharOK_of H0.hmul vec_get (by decide +kernel) (by rw [V0.hI])
    (all_range_blocks (B := 64) (n := 16) H0.blocks)

end CertificateChecks.KernelO8.SB3880

end
