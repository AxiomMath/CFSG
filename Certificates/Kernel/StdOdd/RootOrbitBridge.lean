module

public import Certificates.Kernel.Misc.E6StdBlow
public import CFSG.Certificates.Kernel.StdOdd.RootOrbitSound

public section

namespace CFSG.KD.StdOdd.Orbit

open CFSG.KC.StdOdd.Orbit CFSG.KS.StdOdd.Orbit CFSG.KC.Misc.E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel Matrix

@[expose] noncomputable def ptK (PL : List ℕ) (i : ℕ) : Fin 78 → K :=
  fun k => ofBits ((nthN PL (2 * k)).testBit i) ((nthN PL (2 * k + 1)).testBit i)

@[expose] def flat (x : Fin 78 → K) : Fin 156 → ZMod 2 :=
  fun j => blkF (x (eqv.symm j).1) (eqv.symm j).2 0

theorem flat_eqv (x : Fin 78 → K) (k : Fin 78) (a : Fin 2) :
    flat x (eqv (k, a)) = blkF (x k) a 0 := by
  simp only [flat, Equiv.symm_apply_apply]

theorem flat_mulVec (M : Matrix (Fin 78) (Fin 78) K) (x : Fin 78 → K) :
    flat (M *ᵥ x) = blowM M *ᵥ flat x := by
  ext j
  obtain ⟨⟨k, a⟩, rfl⟩ := eqv.surjective j
  have e1 : blkF ((M *ᵥ x) k) = ∑ l, blkF (M k l) * blkF (x l) := by
    change blkHom (∑ l, M k l * x l) = ∑ l, blkHom (M k l) * blkHom (x l)
    rw [map_sum]
    simp only [map_mul]
  rw [flat_eqv, e1, Matrix.sum_apply, Matrix.mulVec, dotProduct, ← eqv.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [blowM_apply, flat_eqv]

theorem blkF_col_inj {x y : K} (h0 : blkF x 0 0 = blkF y 0 0) (h1 : blkF x 1 0 = blkF y 1 0) :
    x = y := by
  have e : ∀ z : K, blkF z 0 1 = blkF z 1 0 := fun _ => rfl
  rw [← unblk_blkF x, ← unblk_blkF y]
  simp only [unblk, h0, e x, e y, h1]

theorem flat_inj {x y : Fin 78 → K} (h : flat x = flat y) : x = y := by
  funext k
  have h0 := congrFun h (eqv (k, 0))
  have h1 := congrFun h (eqv (k, 1))
  rw [flat_eqv, flat_eqv] at h0 h1
  exact blkF_col_inj h0 h1

theorem toZ_eq_ite (b : Bool) : toZ b = if b then 1 else 0 := rfl

theorem flat_ptK (PL : List ℕ) (i : ℕ) : flat (ptK PL i) = ptB PL i := by
  ext j
  obtain ⟨⟨k, a⟩, rfl⟩ := eqv.surjective j
  rw [flat_eqv]
  simp only [ptK, ptB, blkF_ofBits, eqv_val]
  rcases a with ⟨_ | _ | a, ha⟩
  · simp [bb, toZ_eq_ite]
  · have e : 1 + 2 * (k : ℕ) = 2 * k + 1 := Nat.add_comm _ _
    simp [bb, toZ_eq_ite, e]
  · omega

theorem matB_eq_decB (M : ℕ) : KS.StdOdd.Orbit.matB M = decB M := by
  ext c d
  simp [KS.StdOdd.Orbit.matB, decB, toZ_eq_ite]

theorem step_iff {PL : List ℕ} {A : ℕ} {MA : Native.Mat} (hA : Rep A (toMat MA)) (i j : ℕ) :
    ptB PL j = KS.StdOdd.Orbit.matB A *ᵥ ptB PL i ↔ ptK PL j = toMat MA *ᵥ ptK PL i := by
  rw [matB_eq_decB, hA.2, ← flat_ptK, ← flat_ptK, ← flat_mulVec]
  exact ⟨flat_inj, fun h => by rw [h]⟩

theorem ite_one_zero_inj {b c : Prop} [Decidable b] [Decidable c]
    (h : (if b then (1 : ZMod 2) else 0) = if c then 1 else 0) : (b ↔ c) := by
  by_cases hb : b <;> by_cases hc : c <;> simp_all

theorem ptK_root {PL : List ℕ} {r : ℕ}
    (h : ∀ c : Fin 156, ptB PL r c = if (c : ℕ) = 14 then 1 else 0) :
    ptK PL r = Pi.single 7 1 := by
  funext k
  have h0 := ite_one_zero_inj (h ⟨2 * k, by omega⟩)
  have h1 := ite_one_zero_inj (h ⟨2 * k + 1, by omega⟩)
  have b1 : (nthN PL (2 * (k : ℕ) + 1)).testBit r = false := by
    cases e : (nthN PL (2 * (k : ℕ) + 1)).testBit r
    · rfl
    · exact absurd (h1.1 e) (fun e' => by simp only at e'; omega)
  by_cases hk : (k : ℕ) = 7
  · have b0 : (nthN PL (2 * (k : ℕ))).testBit r = true := h0.2 (by simp only; omega)
    have e : ptK PL r k = ofBits true false := by simp only [ptK, b0, b1]
    have hk' : k = 7 := Fin.ext hk
    rw [e, ofBits_true_false, hk', Pi.single_eq_same]
  · have b0 : (nthN PL (2 * (k : ℕ))).testBit r = false := by
      cases e : (nthN PL (2 * (k : ℕ))).testBit r
      · rfl
      · exact absurd (h0.1 e) (fun e' => by simp only at e'; omega)
    have e : ptK PL r k = ofBits false false := by simp only [ptK, b0, b1]
    rw [e, ofBits_false]
    have hk' : k ≠ 7 := fun h => hk (by rw [h]; rfl)
    exact (Pi.single_eq_of_ne (M := fun _ => K) hk' 1).symm

theorem facts_of_bits {PL : List ℕ} {A B n r : ℕ} {MA MB : Native.Mat}
    (hA : Rep A (toMat MA)) (hB : Rep B (toMat MB)) (h : OrbitBits PL A B n r) :
    ∃ (pts : ℕ → Fin 78 → K) (dep : ℕ → ℕ),
      (∀ i < n, ∀ j < n, pts i = pts j → i = j) ∧
      (∃ r < n, pts r = Pi.single 7 1) ∧
      (∀ i < n, ∃ j < n, pts j = toMat MA *ᵥ pts i) ∧
      (∀ i < n, ∃ j < n, pts j = toMat MB *ᵥ pts i) ∧
      (∀ i < n, dep i = 0 → pts i = Pi.single 7 1) ∧
      (∀ i < n, 0 < dep i → ∃ j < n, dep j < dep i ∧
        (pts i = toMat MA *ᵥ pts j ∨ pts i = toMat MB *ᵥ pts j ∨
          pts j = toMat MB *ᵥ pts i)) := by
  obtain ⟨dep, h0, hs⟩ := h.conn
  have hroot := ptK_root h.root
  refine ⟨ptK PL, dep, fun i hi j hj e => h.inj i hi j hj (by rw [← flat_ptK, ← flat_ptK, e]),
    ⟨r, h.root_lt, hroot⟩, fun i hi => ?_, fun i hi => ?_, fun i hi hd => ?_, fun i hi hd => ?_⟩
  · obtain ⟨j, hj, e⟩ := h.closA i hi
    exact ⟨j, hj, (step_iff hA i j).1 e⟩
  · obtain ⟨j, hj, e⟩ := h.closB i hi
    exact ⟨j, hj, (step_iff hB i j).1 e⟩
  · rw [h0 i hi hd, hroot]
  · obtain ⟨j, hj, hlt, e⟩ := hs i hi hd
    refine ⟨j, hj, hlt, ?_⟩
    rcases e with e | e | e
    · exact Or.inl ((step_iff hA j i).1 e)
    · exact Or.inr (Or.inl ((step_iff hB j i).1 e))
    · exact Or.inr (Or.inr ((step_iff hB i j).1 e))

end CFSG.KD.StdOdd.Orbit

end
