module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGBase
public import Certificates.Data.Kernel.BfsPin

public section

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin Matrix

@[expose] noncomputable def fk (p i : ℕ) : ℕ := pg 3 (mask 3) p i

@[expose] noncomputable def unpk (p : ℕ) : FM := Array.ofFn (n := 25) fun i => fk p i.val

@[expose] noncomputable def entK (p q i j : ℕ) : ℕ :=
  (fk p (5 * i) * fk q j + fk p (5 * i + 1) * fk q (5 + j) + fk p (5 * i + 2) * fk q (10 + j) +
    fk p (5 * i + 3) * fk q (15 + j) + fk p (5 * i + 4) * fk q (20 + j)) % 5

@[expose] noncomputable def mulL (p q : ℕ) : List ℕ :=
  (List.range 25).map fun k => entK p q (k / 5) (k % 5)

@[expose] noncomputable def mulK (p q : ℕ) : ℕ := packA 3 (mulL p q)

@[expose] noncomputable def oneK : ℕ :=
  packA 3 [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]

@[expose] noncomputable def powK (p : ℕ) : ℕ → ℕ
  | 0 => oneK
  | n + 1 => mulK p (powK p n)

theorem pg_mask_eq (w p i : ℕ) : pg w (mask w) p i = p / 2 ^ (w * i) % 2 ^ w := by
  have hm : mask w = 2 ^ w - 1 := by
    change 1 <<< w - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  change (p >>> (w * i)) &&& mask w = _
  rw [hm, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem packA_cons_eq {w x : ℕ} (M : List ℕ) (hx : x < 2 ^ w) :
    packA w (x :: M) = packA w M * 2 ^ w + x := by
  change x ||| (packA w M <<< w) = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]

theorem pg_packA {w : ℕ} : ∀ {M : List ℕ}, (∀ x ∈ M, x < 2 ^ w) →
    ∀ i (hi : i < M.length), pg w (mask w) (packA w M) i = M[i]
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | x :: M, h, i, hi => by
    have hx := h x List.mem_cons_self
    rw [pg_mask_eq, packA_cons_eq M hx]
    rcases i with _ | i
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_comm, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hx, List.getElem_cons_zero]
    · have e : 2 ^ (w * (i + 1)) = 2 ^ w * 2 ^ (w * i) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
      rw [e, ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
        Nat.div_eq_of_lt hx, Nat.zero_add, ← pg_mask_eq, List.getElem_cons_succ]
      exact pg_packA (fun y hy => h y (List.mem_cons_of_mem x hy)) i (Nat.lt_of_succ_lt_succ hi)

theorem unpk_getD (p : ℕ) {i : ℕ} (hi : i < 25) : (unpk p).getD i 0 = fk p i := by
  simp [unpk, Array.getD_eq_getD_getElem?, hi]

theorem mulL_length (p q : ℕ) : (mulL p q).length = 25 := by simp [mulL]

theorem mulL_lt (p q : ℕ) : ∀ x ∈ mulL p q, x < 2 ^ 3 := by
  intro x hx
  simp only [mulL, List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)

theorem fk_mulK (p q : ℕ) {k : ℕ} (hk : k < 25) : fk (mulK p q) k = entK p q (k / 5) (k % 5) := by
  unfold fk mulK
  rw [pg_packA (mulL_lt p q) k (by rw [mulL_length]; exact hk)]
  simp [mulL]

theorem fmMul_unpk (p q : ℕ) : fmMul (unpk p) (unpk q) = unpk (mulK p q) := by
  have hL : fmMul (unpk p) (unpk q) =
      Array.ofFn (n := 25) fun k => fmEntry (unpk p) (unpk q) (k.val / 5) (k.val % 5) := rfl
  have hR : unpk (mulK p q) = Array.ofFn (n := 25) fun k => fk (mulK p q) k.val := rfl
  refine (hL.trans ?_).trans hR.symm
  refine congrArg (Array.ofFn (n := 25)) (funext fun kk => ?_)
  obtain ⟨k, hk⟩ := kk
  refine Eq.trans ?_ (fk_mulK p q hk).symm
  · have hi : k / 5 < 5 := by omega
    have hj : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
    unfold fmEntry entK
    simp (disch := omega) only [unpk_getD]

theorem fmOne_eq : fmOne = unpk oneK := by decide +kernel

theorem fmPow_unpk (p : ℕ) : ∀ n, fmPow (unpk p) n = unpk (powK p n)
  | 0 => fmOne_eq
  | n + 1 => by rw [fmPow, powK, fmPow_unpk p n, fmMul_unpk]

theorem unpk_packA_inj {L M : List ℕ} (hL : L.length = 25) (hM : M.length = 25)
    (hL8 : ∀ x ∈ L, x < 2 ^ 3) (hM8 : ∀ x ∈ M, x < 2 ^ 3)
    (h : unpk (packA 3 L) = unpk (packA 3 M)) : packA 3 L = packA 3 M := by
  congr 1
  apply List.ext_getElem (hL.trans hM.symm)
  intro i h1 h2
  have hi : i < 25 := hL ▸ h1
  have e := congrArg (fun a : FM => a.getD i 0) h
  simp only [unpk_getD _ hi, fk] at e
  rwa [pg_packA hL8 i h1, pg_packA hM8 i h2] at e

theorem mulK_inj {p q p' q' : ℕ} (h : unpk (mulK p q) = unpk (mulK p' q')) :
    mulK p q = mulK p' q' :=
  unpk_packA_inj (mulL_length p q) (mulL_length p' q') (mulL_lt p q) (mulL_lt p' q') h

theorem oneK_inj {p q : ℕ} (h : unpk (mulK p q) = unpk oneK) : mulK p q = oneK :=
  unpk_packA_inj (mulL_length p q) rfl (mulL_lt p q) (by decide) h

theorem fmMul_eq_iff (p q p' q' : ℕ) :
    fmMul (unpk p) (unpk q) = fmMul (unpk p') (unpk q') ↔ mulK p q = mulK p' q' := by
  rw [fmMul_unpk, fmMul_unpk]
  exact ⟨mulK_inj, fun h => by rw [h]⟩

theorem fmMul_eq_one_iff (p q : ℕ) : fmMul (unpk p) (unpk q) = fmOne ↔ mulK p q = oneK := by
  rw [fmMul_unpk, fmOne_eq]
  exact ⟨oneK_inj, fun h => by rw [h]⟩

theorem isSO5_fmMul {a b : FM} (ha : IsSO5 (toM a)) (hb : IsSO5 (toM b)) :
    IsSO5 (toM (fmMul a b)) := by
  rw [toM_fmMul]
  refine ⟨?_, by rw [Matrix.det_mul, ha.2, hb.2, one_mul]⟩
  rw [Matrix.transpose_mul]
  calc (toM b)ᵀ * (toM a)ᵀ * soGram5 * (toM a * toM b)
      = (toM b)ᵀ * ((toM a)ᵀ * soGram5 * toM a) * toM b := by simp only [Matrix.mul_assoc]
    _ = soGram5 := by rw [ha.1, hb.1]

end CertificateChecks.KernelTwoHSLe4.SO5

end
