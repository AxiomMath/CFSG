module

public import Certificates.Kernel.OmegaEight.SB3872

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

set_option maxHeartbeats 0 in
theorem kill_inv : invOK mulK invK 65536 = true := by
  unfold invOK
  refine all_range_chunks 16384 4 fun s hs => ?_
  interval_cases s <;> decide +kernel

set_option maxHeartbeats 0 in
theorem kill_chi : chiOK mulK sGens 65536 (chiB 9) (chiS 65536) = true := by
  unfold chiOK
  simp only [chiS_size, chiS_get, Bool.and_eq_true]
  refine ⟨⟨by decide, by decide +kernel⟩, ?_⟩
  refine all_range_chunks 8192 8 fun s hs => ?_
  interval_cases s <;> decide +kernel

theorem kX_eq (ti : ℕ × ℕ) (X : List ℕ)
    (h : ∀ s < 12, ((rLit.getD s 0 :: []).filter fun u =>
      kCount mulK sInvListLit u == ti.1 && kCount mulK oLit u == ti.2) =
        if X.contains (rLit.getD s 0) then [rLit.getD s 0] else [])
    (hX : (rLit.map fun r => if X.contains r then [r] else []).flatten = X) :
    kX mulK sInvListLit oLit rLit ti = X := by
  unfold kX
  rw [(by decide +kernel : rLit = (rLit.map fun r => [r]).flatten), ← hX]
  refine filter_blocks _ _ _ (by simp) fun s hs => ?_
  have hr : rLit.length = 12 := by decide +kernel
  have hs' : s < 12 := by simpa [hr] using hs
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (hr ▸ hs'),
    Option.map_some, Option.getD_some]
  have := h s hs'
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hr ▸ hs'), Option.getD_some]
    using this

set_option maxHeartbeats 0 in
theorem kX_64 : kX mulK sInvListLit oLit rLit (1439, 10336) = xLit.getD 0 [] := by
  refine kX_eq _ _ (fun s hs => ?_) (by decide +kernel)
  interval_cases s <;> decide +kernel

set_option maxHeartbeats 0 in
theorem kX_75 : kX mulK sInvListLit oLit rLit (1439, 9312) = xLit.getD 1 [] := by
  refine kX_eq _ _ (fun s hs => ?_) (by decide +kernel)
  interval_cases s <;> decide +kernel

set_option maxHeartbeats 0 in
theorem kill_at (t : ℕ × (ℕ × ℕ)) (ht : t ∈ sMarked) :
    killAt mulK invK sGens 65536 sInvListLit oLit rLit 4 (chiS 65536) false t.1 t.2 = true := by
  simp only [sMarked, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · unfold killAt
    rw [kX_64]
    simp only [chiS_get]
    decide +kernel
  · unfold killAt
    rw [kX_75]
    simp only [chiS_get]
    decide +kernel

end CertificateChecks.KernelO8.SB3872

end
