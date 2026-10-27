module

public import Certificates.Kernel.Fi22Twist.SrchFacts
public import Certificates.Kernel.Sporadic.Fi22.N3153Final

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.KS.Raw
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor

set_option maxRecDepth 400000


theorem fld1 (N y : ℕ) : fld(N, y, 1) = (N.testBit y).toNat := by
  have h : Nat.testBit N y = ((N >>> y) &&& 1 != 0) := by
    unfold Nat.testBit
    rw [Nat.and_comm]
  rw [h]
  change (N >>> y) &&& 1 = _
  have hl : (N >>> y) &&& 1 ≤ 1 := Nat.and_le_right
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl with e | e <;> rw [e] <;> rfl

theorem eb_inv {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P) :
    ∀ x < 3510, ∀ y < 3510, eb CFSG.KD.N3153.M (pt (MonoidHom.id _) g x)
      (pt (MonoidHom.id _) g y) = eb CFSG.KD.N3153.M x y := by
  intro x hx y hy
  have hinv := (CFSG.Certificates.adjFacts_of_adjOK N3153.adj).inv_of_mem_closure
    rep_fi22OrigArrs_nat (fi22P_eq_closure_gens ▸ hg)
  have k := hinv ⟨x, hx⟩ ⟨y, hy⟩
  rw [N3153.nbr_eq, CFSG.KC.Fi22Snd.rowsArr_get hx,
    CFSG.KC.Fi22Snd.rowsArr_get (g ⟨x, hx⟩).2] at k
  unfold eb
  rw [fld1, fld1, pt, pt, dif_pos hx, dif_pos hy, MonoidHom.id_apply,
    CFSG.KC.Fi22Snd.row_mask (N3153.rows _ (g ⟨x, hx⟩).2), CFSG.KC.Fi22Snd.row_mask (N3153.rows x hx)]
  change (decide (((g ⟨y, hy⟩ : Fin 3510) : ℕ) ∈ _)).toNat = (decide (y ∈ _)).toNat
  rw [decide_eq_decide.2 k.symm]

theorem d_comm {j : ℕ} (hj : j < 5) {g : Equiv.Perm (Fin 3510)}
    (hc : ∀ y ∈ dSub j, g * y = y * g) :
    ∀ e < 27, ∀ x < 3510, pt (MonoidHom.id _) g (ap (DF (27 * j + e)) x) =
      ap (DF (27 * j + e)) (pt (MonoidHom.id _) g x) := by
  intro e he x hx
  obtain ⟨y, hy, hyz⟩ := df_mem hj e he
  rw [hyz x hx, hyz _ (pt_lt _ _ hx), ← pt_mul, ← pt_mul, hc y hy]

theorem d_lt {j : ℕ} (hj : j < 5) : ∀ e < 27, ∀ x < 3510, ap (DF (27 * j + e)) x < 3510 := by
  intro e he x hx
  obtain ⟨y, -, hyz⟩ := df_mem hj e he
  rw [hyz x hx]
  exact pt_lt _ _ hx

theorem jx_rel {j : ℕ} (hj : j < 5) :
    (∀ d < 3, relV (fun e => DF (Nat.add (Nat.mul 27 j) e))
      (fld(GF j, Nat.mul 1024 d, Nat.sub (Nat.shiftLeft 1 1024) 1)) d = true) ∧
    relV (fun e => DF (Nat.add (Nat.mul 27 j) e))
      (fld(HF j, 0, Nat.sub (Nat.shiftLeft 1 256) 1)) 3 = true ∧
    relV (fun e => DF (Nat.add (Nat.mul 27 j) e)) (Nat.shiftRight (HF j) 256) 4 = true ∧
    relV (fun e => DF (Nat.add (Nat.mul 27 j) e)) (XF j) 5 = true := by
  have h := jx431009All j hj
  unfold ch431009jx_ at h
  beta_reduce at h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  rw [CFSG.KC.Fi22Twist.strictB_eq, CFSG.KC.Fi22Twist.strictB_eq] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  exact ⟨fun d hd => allBlk_spec0 h1 d hd, h2, h3, h4⟩

theorem land_mask (N d : ℕ) :
    Nat.land N (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1) = N % 2 ^ (12 * d) := by
  change N &&& (1 <<< (12 * d) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem node_cs {x0 x1 v d : ℕ} (hd : d ≤ 2) (h0 : 0 < d → x0 < 4096) (h1 : 1 < d → x1 < 4096)
    (hv : v < 4096) :
    (0 < d → cg (Nat.land (Nat.lor x0 (Nat.shiftLeft x1 12))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) 0 = x0) ∧
    (1 < d → cg (Nat.land (Nat.lor x0 (Nat.shiftLeft x1 12))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) 1 = x1) ∧
    (0 < d → cg (Nat.lor (Nat.land (Nat.lor x0 (Nat.shiftLeft x1 12))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) (Nat.shiftLeft v (Nat.mul 12 d))) 0 = x0) ∧
    (1 < d → cg (Nat.lor (Nat.land (Nat.lor x0 (Nat.shiftLeft x1 12))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) (Nat.shiftLeft v (Nat.mul 12 d))) 1 = x1) ∧
    cg (Nat.lor (Nat.land (Nat.lor x0 (Nat.shiftLeft x1 12))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) (Nat.shiftLeft v (Nat.mul 12 d))) d = v := by
  rw [land_mask]
  have hA : Nat.lor x0 (Nat.shiftLeft x1 12) % 2 ^ (12 * d) < 2 ^ (Nat.mul 12 d) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have e1 := or_shift (x := v) hA
  change Nat.lor _ (Nat.shiftLeft v (Nat.mul 12 d)) = _ at e1
  rw [e1, cg_eq, cg_eq, cg_eq, cg_eq, cg_eq]
  interval_cases d
  · simp only [Nat.mul_eq, Nat.reduceMul, Nat.reducePow, Nat.mod_one, Nat.zero_add, Nat.pow_zero,
      Nat.div_one, Nat.one_mul]
    refine ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num),
      fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), ?_⟩
    omega
  · have hx0 := h0 (by norm_num)
    have a0 : x0 < 2 ^ 12 := by simpa using hx0
    have e0 := or_shift (x := x1) a0
    change Nat.lor x0 (Nat.shiftLeft x1 12) = _ at e0
    rw [e0]
    simp only [Nat.mul_eq, Nat.reduceMul, Nat.reducePow]
    refine ⟨fun _ => by omega, fun h => absurd h (by norm_num), fun _ => by omega,
      fun h => absurd h (by norm_num), by omega⟩
  · have hx0 := h0 (by norm_num)
    have hx1 := h1 (by norm_num)
    have a0 : x0 < 2 ^ 12 := by simpa using hx0
    have e0 := or_shift (x := x1) a0
    change Nat.lor x0 (Nat.shiftLeft x1 12) = _ at e0
    rw [e0]
    simp only [Nat.mul_eq, Nat.reduceMul, Nat.reducePow]
    refine ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega, fun _ => by omega, by omega⟩

theorem pass_node {M Dj : ℕ → ℕ} {a φ : ℕ → ℕ} {H d k : ℕ} (hd : d ≤ 2) (hR : RelV Dj H d)
    (hg : ∀ x < 3510, φ x < 3510)
    (hadj : ∀ x < 3510, ∀ y < 3510, eb M (φ x) (φ y) = eb M x y)
    (hD : ∀ e < 27, ∀ x < 3510, φ (ap (Dj e) x) = ap (Dj e) (φ x))
    (hDlt : ∀ e < 27, ∀ x < 3510, ap (Dj e) x < 3510)
    (hc : ∀ m < d, a (bp m) = φ (bp m)) (hv : a (ap (OF d) k) = φ (bp d)) :
    passL Dj a (OF d)
      (maskL M Dj (Nat.land (Nat.lor (a (bp 0)) (Nat.shiftLeft (a (bp 1)) 12))
        (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) d d) H
      (Nat.land (Nat.lor (a (bp 0)) (Nat.shiftLeft (a (bp 1)) 12))
        (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) d k = true := by
  have hb : ∀ m ≤ 4, φ (bp m) < 4096 := fun m hm => Nat.lt_trans (hg _ (bp_lt m hm)) (by norm_num)
  obtain ⟨c0, c1, c0', c1', cd⟩ := node_cs (x0 := a (bp 0)) (x1 := a (bp 1)) (v := φ (bp d)) hd
    (fun h => by rw [hc 0 h]; exact hb 0 (by norm_num))
    (fun h => by rw [hc 1 h]; exact hb 1 (by norm_num)) (hb d (by omega))
  have k1 : ∀ m < d, cg (Nat.land (Nat.lor (a (bp 0)) (Nat.shiftLeft (a (bp 1)) 12))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) m = φ (bp m) := by
    intro m hm
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · rw [c0 hm, hc 0 hm]
    · rw [c1 hm, hc 1 hm]
  have k2 : ∀ l ≤ d, cg (Nat.lor (Nat.land (Nat.lor (a (bp 0)) (Nat.shiftLeft (a (bp 1)) 12))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) (Nat.shiftLeft (φ (bp d)) (Nat.mul 12 d))) l =
      φ (bp l) := by
    intro l hl
    rcases Nat.lt_or_ge l d with hlt | hge
    · obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
      · rw [c0' hlt, hc 0 hlt]
      · rw [c1' hlt, hc 1 hlt]
    · obtain rfl : l = d := by omega
      exact cd
  have m1 : fld(maskL M Dj (Nat.land (Nat.lor (a (bp 0)) (Nat.shiftLeft (a (bp 1)) 12))
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul 12 d)) 1)) d d, φ (bp d), 1) = 1 := by
    rw [maskL_bit _ _ _ _ _ _ (hg _ (bp_lt d (by omega)))]
    intro m hm e he
    rw [k1 m hm, ← hD e he _ (bp_lt m (by omega)),
      hadj _ (hDlt e he _ (bp_lt m (by omega))) _ (bp_lt d (by omega))]
  have r1 := relK_intro hR k2 fun e he l hl => hD e he _ (bp_lt l (by omega))
  unfold passL
  rw [strictB_eqL, hv, m1, r1]
  rfl

@[expose] noncomputable def aN (r x : ℕ) : ℕ :=
  nIf(Nat.beq (fld(r, 48, 255)) 0, x,
    ap (TC (fld(r, 0, 65535))) (nIf(Nat.beq (fld(r, 48, 255)) 1, x, ap (TC (fld(r, 16, 65535))) x)))

theorem node_step {j n : ℕ} (hj : j < 5) (hn : n < 212) (hjn : fld(LF n, 56, 255) = j)
    {g : Equiv.Perm (Fin 3510)} (hgP : g ∈ fi22P) (hc : ∀ y ∈ dSub j, g * y = y * g)
    {α : Equiv.Perm (Fin 3510)} (hα : α ∈ fi22P)
    (ha : ∀ x < 3510, aN (LF n) x = pt (MonoidHom.id _) α x)
    (hfix : ∀ m < fld(LF n, 48, 255), pt (MonoidHom.id _) α (bp m) = pt (MonoidHom.id _) g (bp m)) :
    fld(LF n, 48, 255) < 3 ∧ ∃ t < fld(LF n, 80, 255),
      (∀ mm < fld(LF n, 48, 255),
        fld(nIf(Nat.blt (fld(LF n, 48, 255)) 2, LF (Nat.add (fld(LF n, 64, 65535)) t),
          CFSG.KD.Fi22Twist.KF (Nat.add (fld(LF n, 64, 65535)) t)), Nat.mul 16 mm, 65535) =
          fld(LF n, Nat.mul 16 mm, 65535)) ∧
      (fld(LF n, 48, 255) < 2 →
        fld(LF (Nat.add (fld(LF n, 64, 65535)) t), 48, 255) = Nat.succ (fld(LF n, 48, 255)) ∧
        fld(LF (Nat.add (fld(LF n, 64, 65535)) t), 56, 255) = j) ∧
      (¬ fld(LF n, 48, 255) < 2 → offK j ≤ Nat.add (fld(LF n, 64, 65535)) t ∧
        Nat.add (fld(LF n, 64, 65535)) t < offK (Nat.succ j)) ∧
      fld(nIf(Nat.blt (fld(LF n, 48, 255)) 2, LF (Nat.add (fld(LF n, 64, 65535)) t),
          CFSG.KD.Fi22Twist.KF (Nat.add (fld(LF n, 64, 65535)) t)),
        Nat.mul 16 (fld(LF n, 48, 255)), 65535) < 891 ∧
      ∃ α' ∈ fi22P, (∀ x < 3510, aN (LF n) (ap (TC (fld(nIf(Nat.blt (fld(LF n, 48, 255)) 2,
          LF (Nat.add (fld(LF n, 64, 65535)) t),
          CFSG.KD.Fi22Twist.KF (Nat.add (fld(LF n, 64, 65535)) t)),
          Nat.mul 16 (fld(LF n, 48, 255)), 65535))) x) = pt (MonoidHom.id _) α' x) ∧
        ∀ m ≤ fld(LF n, 48, 255), pt (MonoidHom.id _) α' (bp m) = pt (MonoidHom.id _) g (bp m) := by
  obtain ⟨hd3, -, hall⟩ := nodeK_sound (nd_all n hn)
  rw [hjn] at hall
  refine ⟨hd3, ?_⟩
  generalize hdd : fld(LF n, 48, 255) = d at hall hfix hd3 ⊢
  have hd6 : d < 6 := by omega
  have hfix' : ∀ m < d, pt (MonoidHom.id _) (α⁻¹ * g) (bp m) = bp m := by
    intro m hm
    rw [pt_mul, ← hfix m hm, ← pt_mul, inv_mul_cancel, pt_one]
  obtain ⟨k, hk, hkv⟩ := lv_orbit hd6 (mul_mem (inv_mem hα) hgP) hfix'
  have hb := lv_base (lv_all (20 * d + 19) (by omega))
  have hok : ap (OF d) k < 3510 := (hb.2 k hk).1
  have hv : aN (LF n) (ap (OF d) k) = pt (MonoidHom.id _) g (bp d) := by
    rw [ha _ hok, hkv, ← pt_mul, mul_inv_cancel_left]
  have hc' : ∀ m < d, aN (LF n) (bp m) = pt (MonoidHom.id _) g (bp m) := by
    intro m hm
    rw [ha _ (bp_lt m (by omega)), hfix m hm]
  have hR := relV_sound ((jx_rel hj).1 d hd3)
  have hlam : ∀ x, nIf(Nat.beq d 0, x, ap (TC (fld(LF n, 0, 65535)))
      (nIf(Nat.beq d 1, x, ap (TC (fld(LF n, 16, 65535))) x))) = aN (LF n) x := by
    intro x
    unfold aN
    rw [hdd]
  have hp := pass_node (M := CFSG.KD.N3153.M) (a := fun x => nIf(Nat.beq d 0, x,
      ap (TC (fld(LF n, 0, 65535))) (nIf(Nat.beq d 1, x, ap (TC (fld(LF n, 16, 65535))) x))))
    (k := k) (by omega) hR (fun x hx => pt_lt _ _ hx) (eb_inv hgP) (d_comm hj hc) (d_lt hj)
    (fun m hm => (hlam (bp m)).trans (hc' m hm)) ((hlam _).trans hv)
  obtain ⟨t, ht, hft, hch⟩ := hall k hk hp
  refine ⟨t, ht, ?_⟩
  unfold childL at hch
  simp only [strictB_eqL] at hch
  obtain ⟨h1, hch⟩ := (bAnd_iff _ _).1 hch
  obtain ⟨h2, hch⟩ := (bAnd_iff _ _).1 hch
  obtain ⟨h3, hch⟩ := (bAnd_iff _ _).1 hch
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 hch
  generalize hci : Nat.add (fld(LF n, 64, 65535)) t = ci at h1 h2 h3 h4 h5 ⊢
  generalize hcc : nIf(Nat.blt d 2, LF ci, CFSG.KD.Fi22Twist.KF ci) = c at h1 h2 h3 h4 h5 ⊢
  have hfi : fld(c, Nat.mul 16 d, 65535) < 891 := Nat.le_of_ble_eq_true h4
  obtain ⟨q1, q2, q3, q4⟩ := tfPt_sound (tp_all _ hfi)
  have hlev : fld(TTC (fld(c, Nat.mul 16 d, 65535)), 0, 255) = d := Nat.eq_of_beq_eq_true h2
  have hpt : fld(TTC (fld(c, Nat.mul 16 d, 65535)), 8, 65535) = k := by
    have e := Nat.eq_of_beq_eq_true h3
    rw [hft] at e
    exact Nat.succ.inj e
  rw [hlev, hpt] at q3
  rw [hlev] at q4
  refine ⟨fun mm hmm => Nat.eq_of_beq_eq_true (allBlk_spec0 h1 mm hmm), fun hd2 => ?_,
    fun hd2 => ?_, hfi, ?_⟩
  · have hc2 : c = LF ci := by
      rw [← hcc, blt_tt hd2]
    rw [blt_tt hd2, hc2] at h5
    obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 h5
    exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2⟩
  · rw [blt_ff (a := d) (b := 2) (by omega)] at h5
    obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 h5
    exact ⟨Nat.le_of_ble_eq_true e1, Nat.le_of_ble_eq_true e2⟩
  · obtain ⟨s, hs, hsx⟩ := tc_mem _ hfi
    refine ⟨α * s, mul_mem hα hs, fun x hx => ?_, fun m hm => ?_⟩
    · rw [hsx x hx, ha _ (pt_lt _ _ hx), pt_mul]
    · rw [pt_mul, ← hsx _ (bp_lt m (by omega))]
      rcases Nat.lt_or_ge m d with hlt | hge
      · rw [q4 m hlt, hfix m hlt]
      · obtain rfl : m = d := by omega
        rw [q3, ← ha _ hok, hv]

end CertificateChecks.KernelFi22Twist

end
