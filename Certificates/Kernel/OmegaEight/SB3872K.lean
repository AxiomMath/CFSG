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

theorem mulK_split (c d : ℕ) : ∃ a M, a < 128 ∧ M < 512 ∧
    mulK c d = (c % 128 ^^^ a) + 128 * M ∧ mulK (128 * (c / 128)) d = a + 128 * M := by
  have e1 : 128 * (c / 128) / 2 ^ 7 % 512 = c / 2 ^ 7 % 512 := by omega
  have e2 : 128 * (c / 128) % 128 = 0 := by omega
  unfold mulK sMulG
  simp only [strictN_eq', l127, l511, shr_eq, e1, e2]
  have z : ∀ x : ℕ, Nat.xor 0 x = x := fun x => Nat.zero_xor x
  exact ⟨_, _, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), rfl, by rw [z]; rfl⟩

theorem chi_row (x y : ℕ) (hx : x < 128) (hy : y < 512) :
    (chiS 65536)[x + 128 * y]! = (sNfRow y).testBit (16 * x + 1) := by
  have hlt : x + 128 * y < 65536 := by omega
  rw [chiS_get, Nat.mod_eq_of_lt hlt, decide_eq_true hlt, Bool.true_and]
  unfold nfEK nfEG
  rw [nIf_blt, ite_eq_left hlt]
  simp only [l127, shr_eq, Nat.mul_eq]
  have e1 : (x + 128 * y) / 2 ^ 7 = y := by omega
  have e2 : (x + 128 * y) % 128 = x := by omega
  have h128 : (128 : ℕ) = 2 ^ 7 := by norm_num
  rw [e1, e2, h128, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm 1]
  rfl

@[expose] def sChiMask : ℕ := 2 * ((2 ^ 2048 - 1) / 65535)

theorem sChiMask_bit : ∀ x < 128, sChiMask.testBit (16 * x + 1) = true := by
  have h : ((List.range 128).all fun x => sChiMask.testBit (16 * x + 1)) = true := by
    decide +kernel
  intro x hx
  exact List.all_eq_true.1 h x (List.mem_range.2 hx)

theorem chi_rows : ∀ y < 512, sNfRow y &&& sChiMask =
    (sNfRow 0 &&& sChiMask) ^^^ (if (sNfRow y).testBit 1 then sChiMask else 0) := by
  have h : ((List.range 512).all fun y => sNfRow y &&& sChiMask ==
      ((sNfRow 0 &&& sChiMask) ^^^ (if (sNfRow y).testBit 1 then sChiMask else 0))) = true := by
    decide +kernel
  intro y hy
  simpa using List.all_eq_true.1 h y (List.mem_range.2 hy)

theorem chi_lowHigh : ∀ x < 128, ∀ y < 512,
    (chiS 65536)[x + 128 * y]! = ((chiS 65536)[x]! ^^ (chiS 65536)[128 * y]!) := by
  intro x hx y hy
  have h0 := chi_row x 0 hx (by norm_num)
  have h1 := chi_row 0 y (by norm_num) hy
  rw [Nat.mul_zero, Nat.add_zero] at h0
  rw [Nat.zero_add, Nat.mul_zero, Nat.zero_add] at h1
  rw [chi_row x y hx hy, h0, h1]
  have := congrArg (fun r => r.testBit (16 * x + 1)) (chi_rows y hy)
  simp only [Nat.testBit_land, sChiMask_bit x hx, Bool.and_true, Nat.testBit_xor] at this
  rw [this]
  cases (sNfRow y).testBit 1 <;> simp [sChiMask_bit x hx]

set_option maxHeartbeats 0 in
theorem chi_xor : ∀ x < 128, ∀ y < 128,
    (chiS 65536)[x ^^^ y]! = ((chiS 65536)[x]! ^^ (chiS 65536)[y]!) := by
  have h : ((List.range 128).all fun x => (List.range 128).all fun y =>
      (chiS 65536)[x ^^^ y]! == ((chiS 65536)[x]! ^^ (chiS 65536)[y]!)) = true := by
    simp only [chiS_get]
    decide +kernel
  intro x hx y hy
  simpa using List.all_eq_true.1 (List.all_eq_true.1 h x (List.mem_range.2 hx)) y
    (List.mem_range.2 hy)

set_option maxHeartbeats 0 in
theorem chi_high : ∀ g < 512, ∀ j < 9, (chiS 65536)[mulK (128 * g) (sGens.getD j 0)]! =
    ((chiS 65536)[128 * g]! ^^ (chiB 9).getD j false) := by
  have h : ((List.range 512).all fun g => (List.range 9).all fun j =>
      (chiS 65536)[mulK (128 * g) (sGens.getD j 0)]! ==
        ((chiS 65536)[128 * g]! ^^ (chiB 9).getD j false)) = true := by
    simp only [chiS_get]
    decide +kernel
  intro g hg j hj
  simpa using List.all_eq_true.1 (List.all_eq_true.1 h g (List.mem_range.2 hg)) j
    (List.mem_range.2 hj)

theorem chi_pt (c : ℕ) (hc : c < 65536) (j : ℕ) (hj : j < 9) :
    (chiS 65536)[mulK c (sGens.getD j 0)]! = ((chiS 65536)[c]! ^^ (chiB 9).getD j false) := by
  obtain ⟨a, M, ha, hM, h1, h2⟩ := mulK_split c (sGens.getD j 0)
  have hx : c % 128 ^^^ a < 128 := Nat.xor_lt_two_pow (n := 7) (Nat.mod_lt _ (by norm_num)) ha
  have e4 := chi_high (c / 128) (by omega) j hj
  rw [h2, chi_lowHigh a ha M hM] at e4
  have e5 := chi_lowHigh (c % 128) (Nat.mod_lt _ (by norm_num)) (c / 128) (by omega)
  rw [Nat.mod_add_div] at e5
  rw [h1, chi_lowHigh _ hx M hM, chi_xor _ (Nat.mod_lt _ (by norm_num)) a ha, Bool.xor_assoc, e4,
    e5, Bool.xor_assoc]

theorem kill_chi : chiOK mulK sGens 65536 (chiB 9) (chiS 65536) = true := by
  unfold chiOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨by simp [chiS_size], by simp only [chiS_get]; decide⟩, ?_⟩
  refine List.all_eq_true.2 fun c hc => List.all_eq_true.2 fun j hj => ?_
  have hj' : j < 9 := by simpa [sGens, sPc] using hj
  rw [chi_pt c (List.mem_range.1 hc) j hj', beq_self_eq_true]

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

@[expose] def kRepCI : List ℕ := [2303, 1439, 1439, 1919, 1919, 1791, 1727, 1727, 1439, 1439, 1727, 1599]

@[expose] def kRepCO : List ℕ := [0, 10336, 9312, 0, 0, 0, 0, 0, 9312, 10336, 0, 0]

set_option maxHeartbeats 0 in
theorem kRepCnt_at (s : ℕ) (hs : s < 12) :
    kCount mulK sInvListLit (rLit.getD s 0) = kRepCI.getD s 0 ∧
      (kRepCI.getD s 0 = 1439 → kCount mulK oLit (rLit.getD s 0) = kRepCO.getD s 0) := by
  interval_cases s <;>
    exact ⟨by decide +kernel, fun h => by first | exact absurd h (by decide) | decide +kernel⟩

theorem kX_rec (b : ℕ) (X : List ℕ)
    (h : ∀ s < 12, (if (kRepCI.getD s 0 == 1439 && kRepCO.getD s 0 == b) = true then
      [rLit.getD s 0] else []) = if X.contains (rLit.getD s 0) then [rLit.getD s 0] else [])
    (hX : (rLit.map fun r => if X.contains r then [r] else []).flatten = X) :
    kX mulK sInvListLit oLit rLit (1439, b) = X := by
  refine kX_eq _ _ (fun s hs => ?_) hX
  obtain ⟨h1, h2⟩ := kRepCnt_at s hs
  rw [← h s hs, List.filter_cons, List.filter_nil, h1]
  by_cases hc : kRepCI.getD s 0 = 1439
  · rw [h2 hc]
  · have hb : (kRepCI.getD s 0 == 1439) = false := by simpa using hc
    simp only [hb, Bool.false_and]

theorem kX_64 : kX mulK sInvListLit oLit rLit (1439, 10336) = xLit.getD 0 [] := by
  refine kX_rec _ _ (fun s hs => ?_) (by decide +kernel)
  interval_cases s <;> decide +kernel

theorem kX_75 : kX mulK sInvListLit oLit rLit (1439, 9312) = xLit.getD 1 [] := by
  refine kX_rec _ _ (fun s hs => ?_) (by decide +kernel)
  interval_cases s <;> decide +kernel

theorem kill_at (t : ℕ × (ℕ × ℕ)) (ht : t ∈ sMarked) :
    killAt mulK invK sGens 65536 sInvListLit oLit rLit 4 (chiS 65536) false t.1 t.2 = true := by
  simp only [sMarked, List.mem_cons, List.not_mem_nil, or_false] at ht
  have h64 := kRepCnt_at 1 (by norm_num)
  have h75 := kRepCnt_at 2 (by norm_num)
  have r1 : rLit.getD 1 0 = 64 := by decide +kernel
  have r2 : rLit.getD 2 0 = 75 := by decide +kernel
  rw [r1] at h64
  rw [r2] at h75
  rcases ht with rfl | rfl
  · unfold killAt
    rw [kX_64, h64.1, h64.2 (by decide)]
    simp only [chiS_get]
    decide +kernel
  · unfold killAt
    rw [kX_75, h75.1, h75.2 (by decide)]
    simp only [chiS_get]
    decide +kernel

end CertificateChecks.KernelO8.SB3872

end
