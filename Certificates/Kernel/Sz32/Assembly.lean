module

public import Certificates.Kernel.Sz32.Chk
public import CFSG.Certificates.Kernel.Sz32TwinSound

public section

namespace CFSG.KC.Sz32T

open CFSG.AGLEmbedding.KFactProofs.Sz32 Matrix

theorem rowsOk_all {j : ℕ} (hj : j < 8) : rowsOk wits j = true := by
  interval_cases j
  exacts [rows_0, rows_1, rows_2, rows_3, rows_4, rows_5, rows_6, rows_7]

theorem lineOk_all {x y : ℕ} (hx : x < 32) (hy : y < 32) : lineOk wits x y = true := by
  have h1 := rowsOk_all (j := x / 4) (by omega)
  rw [rowsOk, allLt_iff] at h1
  have h2 := allLt_iff.1 (h1 (x % 4) (Nat.mod_lt _ (by norm_num))) y hy
  have hx4 : 4 * (x / 4) + x % 4 = x := by omega
  rwa [hx4] at h2

theorem ovoid_check {w : Vec} (hw : w = inftyVec ∨ ∃ u v : F32, w = lineVec u v)
    (ha : OnOmegaGen 2 (Pw w *ᵥ lineVec 1 0)) (hb : OnOmegaGen 2 (Pw w *ᵥ lineVec omega 0)) :
    ∃ k < 25, ∃ l : F32, Pw w = l • g0Mat ^ k := by
  rcases hw with rfl | ⟨u, v, rfl⟩
  · rw [← decV_inftyW] at ha hb ⊢
    have h : wOk inftyW (look wits 1024) = true := infty_ok
    exact wOk_sound chain_ok h ha hb
  · obtain ⟨x, hx, rfl⟩ := dec_surj u
    obtain ⟨y, hy, rfl⟩ := dec_surj v
    rw [← decV_lineW] at ha hb ⊢
    have h : wOk (lineW x y) (look wits (32 * x + y)) = true := lineOk_all hx hy
    exact wOk_sound chain_ok h ha hb

end CFSG.KC.Sz32T

end
