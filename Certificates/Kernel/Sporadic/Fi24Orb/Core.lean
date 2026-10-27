
module

public import Certificates.Kernel.Sporadic.Fi24Orb.Faith

public section

namespace CertificateChecks.KernelFi24Orb

open CertificateChecks.KernelFi24Fix CFSG.KC.Fi24FixC CFSG.KC.Fi24Orb CFSG.KD.Fi24Orb

noncomputable def ptL (k : ℕ) : Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
  if h : k = 0 then (CFSG.Sporadic.Fi24.pt 0).sp else
    if hp : oPar (OL k) < k then (ptL (oPar (OL k))).map (Matrix.mulVecLin
      (if oLab (OL k) = 1 then CFSG.Sporadic.Fi24.mA else CFSG.Sporadic.Fi24.mB)) else ⊥
termination_by k
decreasing_by exact hp

theorem act_uA (W : Submodule (ZMod 3) (Fin 781 → ZMod 3)) :
    act uA W = W.map (Matrix.mulVecLin CFSG.Sporadic.Fi24.mA) := by
  unfold act
  rw [uA_val]

theorem act_uB (W : Submodule (ZMod 3) (Fin 781 → ZMod 3)) :
    act uB W = W.map (Matrix.mulVecLin CFSG.Sporadic.Fi24.mB) := by
  unfold act
  rw [uB_val]

theorem ptL_eq : ∀ k < N, ptL k = f k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [ptL, dif_pos rfl, f_zero]
    · obtain ⟨hp, hl⟩ := tree hk (Nat.pos_iff_ne_zero.1 hpos)
      have hpN : oPar (OL k) < N := by omega
      rw [ptL, dif_neg (Nat.pos_iff_ne_zero.1 hpos), dif_pos hp, ih _ hp hpN]
      rcases hl with ⟨h1, he⟩ | ⟨h2, he⟩
      · rw [if_pos h1, ← act_uA, ← f_α hpN]
        exact congrArg f he
      · rw [if_neg (by omega), ← act_uB, ← f_β hpN]
        exact congrArg f he

theorem ptL_zero : ptL 0 = (CFSG.Sporadic.Fi24.pt 0).sp := by
  rw [ptL, dif_pos rfl]

noncomputable abbrev lvl1 : Subgroup Jc := MulAction.stabilizer Jc (0 : Fin N)

theorem smul_iff_ptL (g : Jc) (i j : Fin N) : g • i = j ↔ act g (ptL i) = ptL j := by
  rw [smul_iff, ptL_eq i i.isLt, ptL_eq j j.isLt]

theorem fi24_core :
    Nat.card Jc = 1255205709190661721292800 ∧ IsSimpleGroup Jc ∧
    ptL 0 = (CFSG.Sporadic.Fi24.pt 0).sp ∧
    (∀ i < N, ∀ j < N, ptL i = ptL j → i = j) ∧
    (∀ k < N, oA (OL k) < N ∧ oA (OL (oA (OL k))) = k ∧
      (ptL k).map (Matrix.mulVecLin CFSG.Sporadic.Fi24.mA) = ptL (oA (OL k))) ∧
    (∀ k < N, oB (OL k) < N ∧ oB (OL (oB (OL (oB (OL k))))) = k ∧
      (ptL k).map (Matrix.mulVecLin CFSG.Sporadic.Fi24.mB) = ptL (oB (OL k))) ∧
    (∀ k < N, 0 < k → oPar (OL k) < k ∧ ((oLab (OL k) = 1 ∧ oA (OL (oPar (OL k))) = k) ∨
      (oLab (OL k) = 2 ∧ oB (OL (oPar (OL k))) = k))) ∧
    (∀ W, (∃ g ∈ Jc, act g (CFSG.Sporadic.Fi24.pt 0).sp = W) ↔ ∃ k < N, ptL k = W) ∧
    (∀ (g : Jc) (i j : Fin N), g • i = j ↔ act g (ptL i) = ptL j) ∧
    FaithfulSMul Jc (Fin N) ∧ MulAction.IsPreprimitive Jc (Fin N) ∧
    Nat.card lvl1 = 4089470473293004800 := by
  refine ⟨card_Jc, isSimpleGroup_Jc, ptL_zero, fun i hi j hj h => ?_, fun k hk => ?_,
    fun k hk => ?_, fun k hk hpos => tree hk (Nat.pos_iff_ne_zero.1 hpos), fun W => ?_,
    smul_iff_ptL, faithful, isPreprimitive, card_M0⟩
  · rw [ptL_eq i hi, ptL_eq j hj] at h
    exact f_inj hi hj h
  · refine ⟨α_lt hk, α_α hk, ?_⟩
    rw [ptL_eq k hk, ptL_eq (oA (OL k)) (α_lt hk), ← act_uA]
    exact (f_α hk).symm
  · refine ⟨β_lt hk, β_β_β hk, ?_⟩
    rw [ptL_eq k hk, ptL_eq (oB (OL k)) (β_lt hk), ← act_uB]
    exact (f_β hk).symm
  · constructor
    · rintro ⟨g, hg, rfl⟩
      have hm : act g root ∈ MulAction.orbit Jc root := ⟨⟨g, hg⟩, rfl⟩
      rw [orbit_Jc] at hm
      obtain ⟨r, hr, e⟩ := hm
      obtain ⟨k, hk, rfl⟩ := NM_surj hr
      exact ⟨k, hk, by rw [ptL_eq k hk]; exact e⟩
    · rintro ⟨k, hk, rfl⟩
      have hm : f k ∈ MulAction.orbit Jc root := by
        rw [orbit_Jc]
        exact ⟨NM k, NM_lt hk, rfl⟩
      obtain ⟨⟨g, hg⟩, e⟩ := hm
      exact ⟨g, hg, by rw [ptL_eq k hk]; exact e⟩

end CertificateChecks.KernelFi24Orb

end
