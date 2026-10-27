
module

public import Certificates.Kernel.Ly3085.ChartGlue

public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open Matrix MulAction

@[expose] def fm (X : ℕ) : Form7 := ⟨Matrix.of fun a b => vec49 X ⟨7 * a.val + b.val, by omega⟩⟩

theorem fm_smM (X : ℕ) : (fm X).M = smM X := by
  ext a b
  simp only [fm, Matrix.of_apply, vec49, smM, ent]
  congr 3
  ring

theorem canon_row {X : ℕ} (h : LCanon 11 7 7 X) : LCanon 11 1 49 X := by
  refine ⟨by rw [show 11 * 49 * 1 = 11 * 7 * 7 by norm_num]; exact h.1, fun i hi j hj => ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  have := h.2 (j / 7) (by omega) (j % 7) (by omega)
  have e : 11 * 7 * (j / 7) + 11 * (j % 7) = 11 * 49 * 0 + 11 * j := by omega
  rwa [e] at this

theorem vec49_inj {X Y : ℕ} (hX : LCanon 11 1 49 X) (hY : LCanon 11 1 49 Y)
    (h : vec49 X = vec49 Y) : X = Y := by
  have e1 : 11 * 49 = 11 * 49 * 1 := by norm_num
  refine lanesW_inj 11 49 X Y (by rw [e1]; exact hX.1) (by rw [e1]; exact hY.1) fun q hq => ?_
  have hfX := hX.2 0 (by norm_num) q hq
  have hfY := hY.2 0 (by norm_num) q hq
  have e := congrFun h ⟨q, hq⟩
  simp only [vec49, ent] at e
  simp only [Nat.mul_zero, Nat.zero_add] at hfX hfY e
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hfX, Nat.mod_eq_of_lt hfY] at e
  exact e

theorem fm_kron {X Y K Q : ℕ} (hK : ∀ i j k l : Fin 7,
      kM K ⟨7 * i + j, by omega⟩ ⟨7 * k + l, by omega⟩ = smM Q i k * smM Q j l)
    (h : vec49 Y = Matrix.vecMul (vec49 X) (kM K)) : (fm Y).M = (smM Q)ᵀ * (fm X).M * smM Q := by
  ext a b
  simp only [fm, Matrix.of_apply]
  rw [h, Matrix.vecMul, dotProduct]
  rw [← (finProdFinEquiv (m := 7) (n := 7)).sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e1 : (⟨7 * i.val + j.val, by omega⟩ : Fin 49) = finProdFinEquiv (i, j) := by
    ext
    rw [finProdFinEquiv_apply_val]
    simp only
    ring
  have hK' := hK i j a b
  rw [e1] at hK'
  rw [hK']
  simp only [Matrix.of_apply]
  rw [e1]
  ring

theorem rOK_kron {R Q KQ KR : ℕ} {ra : Array ℕ} (h : CFSG.KD.LyOm.rOK R Q KQ KR ra = true) :
    kronOK Q Q KQ = true ∧ kronOK R R KR = true := by
  unfold CFSG.KD.LyOm.rOK at h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  exact bAnd_true h

theorem gk_facts
    [LySeed] {l : ℕ} (hl : l < 4) :
    LCanon 11 49 49 (CFSG.KD.LyOm.GK l) ∧ ∀ X Y : ℕ,
      vec49 Y = Matrix.vecMul (vec49 X) (kM (CFSG.KD.LyOm.GK l)) →
      fm Y = (⟨lyLet l, lyLet_mem l⟩ : lyH) • fm X := by
  obtain ⟨-, -, eR0, eQ0⟩ := gen_facts (j := 0) (by norm_num) CFSG.KD.LyOm.r0
  obtain ⟨-, -, eR1, eQ1⟩ := gen_facts (j := 1) (by norm_num) CFSG.KD.LyOm.r1
  obtain ⟨kQ0, kR0⟩ := rOK_kron CFSG.KD.LyOm.r0
  obtain ⟨kQ1, kR1⟩ := rOK_kron CFSG.KD.LyOm.r1
  have key : ∀ (K Q : ℕ) (h : J) (hh : h ∈ lyH), kronOK Q Q K = true →
      smM Q = restr7 h⁻¹ → LCanon 11 49 49 K ∧ ∀ X Y : ℕ,
        vec49 Y = Matrix.vecMul (vec49 X) (kM K) → fm Y = (⟨h, hh⟩ : lyH) • fm X := by
    intro K Q h hh hk hQ
    obtain ⟨cK, eK⟩ := SB3.kronOK_sound hk
    refine ⟨cK, fun X Y hXY => ?_⟩
    ext1
    rw [form7_smul_M, fm_kron eK hXY, hQ]
    rfl
  have i2 : (aStar 2)⁻¹⁻¹ = aStar 2 := inv_inv _
  interval_cases l
  · exact key _ _ (aStar 2) (aStar_mem_lyH le_rfl) kQ0 eQ0
  · exact key _ _ (aStar 3) (aStar_mem_lyH (by norm_num)) kQ1 eQ1
  · exact key _ _ (aStar 2)⁻¹ (lyH.inv_mem (aStar_mem_lyH le_rfl)) kR0 (by rw [inv_inv, eR0])
  · exact key _ _ (aStar 3)⁻¹ (lyH.inv_mem (aStar_mem_lyH (by norm_num))) kR1
      (by rw [inv_inv, eR1])

theorem wordR_nil (mul : ℕ → ℕ → ℕ) (G : ℕ → ℕ) (X : ℕ) : wordR mul G X [] = X := rfl

theorem wordR_cons (mul : ℕ → ℕ → ℕ) (G : ℕ → ℕ) (X l : ℕ) (w : List ℕ) :
    wordR mul G X (l :: w) = wordR mul G (mul X (G l)) w := strictN_eq' _ _

theorem wordR_append (mul : ℕ → ℕ → ℕ) (G : ℕ → ℕ) : ∀ (u v : List ℕ) (X : ℕ),
    wordR mul G X (u ++ v) = wordR mul G (wordR mul G X u) v
  | [], v, X => rfl
  | l :: u, v, X => by
    rw [List.cons_append, wordR_cons, wordR_cons]
    exact wordR_append mul G u v _

set_option maxRecDepth 100000 in
theorem fixBeta_word
    [LySeed] : ∀ (w : List ℕ) (X : ℕ), (∀ l ∈ w, l < 4) →
      LCanon 11 1 49 X →
      LCanon 11 1 49 (wordR (sBlk CFSG.KD.LyOm.SC) CFSG.KD.LyOm.GK X w.reverse) ∧
      fm (wordR (sBlk CFSG.KD.LyOm.SC) CFSG.KD.LyOm.GK X w.reverse) =
        (⟨wordJ w, wordJ_mem w⟩ : lyH) • fm X := by
    intro w
    induction w with
    | nil =>
      intro X _ hX
      refine ⟨hX, ?_⟩
      have h1 : (⟨wordJ [], wordJ_mem []⟩ : lyH) = 1 := Subtype.ext (by
        change (([] : List ℕ).map lyLet).prod = 1
        rw [List.map_nil, List.prod_nil])
      rw [h1, one_smul]
      rfl
    | cons l w ih =>
      intro X hw' hX
      obtain ⟨c1, e1⟩ := ih X (fun l' hl' => hw' l' (List.mem_cons_of_mem _ hl')) hX
      obtain ⟨cK, eK⟩ := gk_facts (hw' l List.mem_cons_self)
      rw [List.reverse_cons, wordR_append, wordR_cons, wordR_nil]
      have hb := sBlk_sound hSC (r := 1) (by norm_num) c1 cK
      refine ⟨hb.1, ?_⟩
      have hv := hb.2 0 (by norm_num)
      simp only [Nat.mul_zero, pow_zero, Nat.div_one] at hv
      have hw : (⟨wordJ (l :: w), wordJ_mem _⟩ : lyH) =
          ⟨lyLet l, lyLet_mem l⟩ * ⟨wordJ w, wordJ_mem w⟩ := Subtype.ext (by
        change ((l :: w).map lyLet).prod = lyLet l * (w.map lyLet).prod
        rw [List.map_cons, List.prod_cons])
      rw [eK _ _ hv, e1, hw, mul_smul]

theorem fixBeta_stab
    [LySeed] {BE : ℕ} {w : List ℕ} (hw : ∀ l ∈ w, l < 4)
    (cBE : LCanon 11 7 7 BE) (h : CFSG.KD.LyOm.fixBeta BE w = true) :
    (⟨wordJ w, wordJ_mem w⟩ : lyH) ∈ stabilizer lyH (fm BE) := by
  obtain ⟨-, e⟩ := fixBeta_word w BE hw (canon_row cBE)
  unfold CFSG.KD.LyOm.fixBeta at h
  rw [beq_eq h] at e
  exact e.symm

theorem small_tree
    [LySeed] {KX PT SG : ℕ → ℕ} {KS : List ℕ} {m n nl BE : ℕ}
    (hm : m = 2) (hK0 : pickL KS 0 = CFSG.KD.LyOm.KQ0) (hK1 : pickL KS 1 = CFSG.KD.LyOm.KQ1)
    (hroot : getRec KX 539 0 = BE) (cBE : LCanon 11 7 7 BE) (hnl : n ≤ 64 * nl)
    (hleaf : ∀ b < nl, sLeaf CFSG.KD.LyOm.SC KX PT KS m n b = true)
    (hsg : ∀ k < n, getRec SG 20 k < n)
    (hsort : ∀ k, k + 1 < n → getRec KX 539 (getRec SG 20 k) < getRec KX 539 (getRec SG 20 (k + 1))) :
    (∀ i < n, fm (getRec KX 539 i) ∈ orbit lyH (fm BE)) ∧
      (∀ i < n, ∀ j < n, fm (getRec KX 539 i) = fm (getRec KX 539 j) → i = j) := by
  have hKs : ∀ s < m, LCanon 11 49 49 (pickL KS s) ∧ ∀ X Y : ℕ,
      vec49 Y = Matrix.vecMul (vec49 X) (kM (pickL KS s)) →
      fm Y = (⟨lyLet s, lyLet_mem s⟩ : lyH) • fm X := by
    intro s hs
    rw [hm] at hs
    interval_cases s
    · rw [hK0]
      exact gk_facts (l := 0) (by norm_num)
    · rw [hK1]
      exact gk_facts (l := 1) (by norm_num)
  have hnode : ∀ i < n, 0 < i → _ := fun i hi hi0 =>
    sLeaf_sound hSC (fun s hs => (hKs s hs).1) (hleaf (i / 64) (by omega)) (r := i % 64)
      (Nat.mod_lt _ (by norm_num)) (by omega) (by omega)
  have e64 : ∀ i, 64 * (i / 64) + i % 64 = i := fun i => by omega
  have hcan : ∀ i < n, LCanon 11 1 49 (getRec KX 539 i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hroot]
        exact canon_row cBE
      · have := (hnode i hi hpos).2.2 (by
          rw [e64]
          exact fun j hj => ih j hj (by omega))
        rw [e64] at this
        exact this.1
  refine ⟨fun i hi => ?_, fun i hi j hj e => ?_⟩
  · refine mem_orbit_of_tree (G := lyH) (fm BE) (fun i => fm (getRec KX 539 i))
      (fun i => fldW (sRec PT i) 0 20) n (by rw [hroot]) (fun i hi0 hi => ?_) i hi
    have h := hnode i hi hi0
    rw [e64] at h
    obtain ⟨hp, hl, hv⟩ := h
    obtain ⟨-, e⟩ := hv (fun j hj => hcan j (by omega))
    exact ⟨hp, _, (hKs _ hl).2 _ _ e⟩
  · refine sorted_inj (getRec KX 539) (fun k => getRec SG 20 k) hsg hsort i hi j hj ?_
    apply vec49_inj (hcan i hi) (hcan j hj)
    funext t
    have := congrArg (fun F : Form7 => F.M ⟨t.val / 7, by omega⟩ ⟨t.val % 7, by omega⟩) e
    simp only [fm, Matrix.of_apply] at this
    have et : (⟨7 * (t.val / 7) + t.val % 7, by omega⟩ : Fin 49) = t := Fin.ext (by simp; omega)
    rw [et] at this
    exact this

end CertificateChecks.KernelLy.Omega

end
