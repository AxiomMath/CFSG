module

public import Certificates.Kernel.Fi23C.Facts
public import Certificates.Kernel.Fi23M.Keys
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib
public import CFSG.Sporadic.Fi23.Class

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23C

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KS.Raw.Orb CFSG.KS.PC
  CFSG.KS.PCC CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CertificateChecks.KernelFi23M
open CFSG.Sporadic.Th (idx_of_lt)

theorem acts_congr {p : Equiv.Perm (Fin 31671)} {f g : Nat → Nat} (hp : ActsAs p f)
    (hfg : ∀ x < 31671, f x = g x) : ActsAs p g := fun x hx => by rw [hp x hx, hfg x hx]

theorem acts_apply {p : Equiv.Perm (Fin 31671)} {f : Nat → Nat} (hp : ActsAs p f) {x : Nat}
    (hx : x < 31671) : p ⟨x, hx⟩ = ⟨f x, by rw [← hp x hx]; exact (p ⟨x, hx⟩).isLt⟩ :=
  Fin.ext (hp x hx)

theorem rep_of_acts {T : Table} {p : Equiv.Perm (Fin 31671)} {f : Nat → Nat} (hp : ActsAs p f)
    (hT : ∀ i < 31671, ap T i = f i) : CFSG.Sporadic.Th.Rep 31671 T p := by
  intro i hi
  rw [idx_of_lt p hi, Equiv.Perm.smul_def, hp i hi, hT i hi]

section


theorem acts_alpha_inv : ActsAs (phiX wα)⁻¹ (tb G 39) :=
  phiX_wα.inv (rng 39 (by norm_num)) fun x hx => (ord_pt hx).1

theorem acts_beta_inv : ActsAs (phiX wβ)⁻¹ (tb G 41) :=
  phiX_wβ.inv (rng 41 (by norm_num)) fun _ hx => binv_right hx

noncomputable abbrev tt (k : ℕ) : PG := tk k * wD * (tk k)⁻¹

noncomputable abbrev cp (k : ℕ) : Equiv.Perm (Fin 31671) := phiX (tt k)

theorem tt_zero : tt 0 = wD := by
  have h0 : phiX (tk 0) ⟨0, hn⟩ = phiX 1 ⟨0, hn⟩ := by
    rw [tk_pt (by norm_num), map_one, Equiv.Perm.one_apply]
  rw [tt, conj_eq h0, one_mul, inv_one, mul_one]

theorem cp_zero : cp 0 = phiX wD := by
  rw [cp, tt_zero]

theorem wD_sq : wD * wD = 1 := by
  apply phiX_injective
  rw [map_mul, map_one]
  exact ActsAs.ext (acts_congr (phiX_wD.mul phiX_wD) fun x hx => d2_facts hx) acts_one

theorem tt_sq (k : ℕ) : tt k * tt k = 1 := by
  have e : tk k * wD * (tk k)⁻¹ * (tk k * wD * (tk k)⁻¹) = tk k * (wD * wD) * (tk k)⁻¹ := by group
  rw [tt, e, wD_sq, mul_one, mul_inv_cancel]

theorem cp_inv (k : ℕ) : (cp k)⁻¹ = cp k := by
  rw [inv_eq_iff_mul_eq_one, cp, ← map_mul, tt_sq, map_one]

theorem tt_eqv (g : PG) {m : ℕ} (hm : m < 31671) :
    tt (phiX g ⟨m, hm⟩).val = g * tt m * g⁻¹ := by
  have h0 : phiX (tk (phiX g ⟨m, hm⟩).val) ⟨0, hn⟩ = phiX (g * tk m) ⟨0, hn⟩ := by
    apply Fin.ext
    rw [tk_pt (phiX g ⟨m, hm⟩).isLt, map_mul, Equiv.Perm.mul_apply, tk_pt hm]
  rw [tt, conj_eq h0]
  group

theorem cp_eqv (g : PG) {m : ℕ} (hm : m < 31671) :
    cp (phiX g ⟨m, hm⟩).val = phiX g * cp m * (phiX g)⁻¹ := by
  rw [cp, tt_eqv g hm, map_mul, map_mul, map_inv]

theorem tt_inj {i j : ℕ} (hi : i < 31671) (hj : j < 31671)
    (h : tt i = tt j) : i = j := by
  apply hinj' i hi j hj
  refine eq_of_mat (key_canon hi) (key_canon hj) ?_
  rw [key_mat hi, key_mat hj]
  exact congrArg (fun x => (σ x).val) h

theorem cp_inj {i j : ℕ} (hi : i < 31671) (hj : j < 31671)
    (h : cp i = cp j) : i = j :=
  tt_inj hi hj (phiX_injective h)

noncomputable abbrev labW (k : ℕ) : PG := if tb G 92 k = 1 then wα else wβ

theorem cp_step {k : ℕ} (hk : k < 31671) (hk0 : k ≠ 0) :
    cp k = phiX (labW k) * cp (tb G 91 k) * (phiX (labW k))⁻¹ := by
  obtain ⟨hp, hA, hB⟩ := tr_pt hk hk0
  have hpN : tb G 91 k < 31671 := by omega
  have e : (phiX (labW k) ⟨tb G 91 k, hpN⟩).val = k := by
    by_cases hl : tb G 92 k = 1
    · rw [labW, if_pos hl, phiX_wα _ hpN, hA hl]
    · rw [labW, if_neg hl, phiX_wβ _ hpN, hB hl]
  rw [← cp_eqv _ hpN, e]

theorem cp_step_a {k : ℕ} (hk : k < 31671) (hk0 : k ≠ 0)
    (hl : tb G 92 k = 1) {x : ℕ} (hx : x < 31671) :
    (cp k ⟨x, hx⟩).val = tb G 39 (cp (tb G 91 k) ⟨tb G 39 x, rng 39 (by norm_num) x hx⟩).val := by
  rw [cp_step hk hk0, labW, if_pos hl, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    acts_apply acts_alpha_inv hx, phiX_wα _ (Fin.isLt _)]

theorem cp_step_b {k : ℕ} (hk : k < 31671) (hk0 : k ≠ 0)
    (hl : tb G 92 k ≠ 1) {x : ℕ} (hx : x < 31671) :
    (cp k ⟨x, hx⟩).val = tb G 40 (cp (tb G 91 k) ⟨tb G 41 x, rng 41 (by norm_num) x hx⟩).val := by
  rw [cp_step hk hk0, labW, if_neg hl, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    acts_apply acts_beta_inv hx, phiX_wβ _ (Fin.isLt _)]

theorem cJ_fuel : ∀ f k, k < f → k < 31671 → ∀ x (hx : x < 31671),
    uF G f k (tb G 43 (uInvF G f k x)) = (cp k ⟨x, hx⟩).val := by
  intro f
  induction f with
  | zero => intro k hk; omega
  | succ f ih =>
    intro k hkf hk x hx
    rw [uF_succ, uInvF_succ]
    by_cases h0 : k = 0
    · subst h0
      rw [if_pos rfl, if_pos rfl, cp_zero]
      exact (phiX_wD x hx).symm
    · rw [if_neg h0, if_neg h0]
      have hp := (tr_pt hk h0).1
      by_cases hl : tb G 92 k = 1
      · rw [if_pos hl, if_pos hl, cp_step_a hk h0 hl hx,
          ih _ (by omega) (by omega) _ (rng 39 (by norm_num) x hx)]
      · rw [if_neg hl, if_neg hl, cp_step_b hk h0 hl hx,
          ih _ (by omega) (by omega) _ (rng 41 (by norm_num) x hx)]

theorem cJ_cp {k x : ℕ} (hk : k < 31671) (hx : x < 31671) :
    cJ G k x = (cp k ⟨x, hx⟩).val := by
  rw [cJ_eq]
  exact cJ_fuel _ k hk hk x hx

theorem cJ_lt {k x : ℕ} (hk : k < 31671) (hx : x < 31671) :
    cJ G k x < 31671 := by
  rw [cJ_cp hk hx]
  exact Fin.isLt _

theorem rep_alpha : CFSG.Sporadic.Th.Rep 31671 orbLit.alpha (phiX wα) :=
  rep_of_acts phiX_wα fun i hi => ap_tabOf 39 hi

theorem rep_beta : CFSG.Sporadic.Th.Rep 31671 orbLit.beta (phiX wβ) :=
  rep_of_acts phiX_wβ fun i hi => ap_tabOf 40 hi

theorem rep_dWord (w : List ℕ) :
    CFSG.Sporadic.Th.Rep 31671 (w.foldr (fun x T => compT 31671 (if x = 0 then orbLit.alpha else orbLit.beta) T)
      (idT 31671)) (phiX (w.map fun x => if x = 0 then wα else wβ).prod) := by
  induction w with
  | nil => simpa using CFSG.Sporadic.Th.Rep.idT (G := Equiv.Perm (Fin 31671)) (n := 31671) (by norm_num)
  | cons x w ih =>
    rw [List.foldr_cons, List.map_cons, List.prod_cons, map_mul]
    refine CFSG.Sporadic.Th.Rep.compT ?_ ih
    split_ifs
    · exact rep_alpha
    · exact rep_beta

theorem acts_dWord : ActsAs (phiX (dWord.map fun x => if x = 0 then wα else wβ).prod) (tb G 42) := by
  intro x hx
  rw [acts_wv dWord x hx]
  have h := eqv (k := 136) (by norm_num) hx
  rw [eq136.1, eq136.2] at h
  simp only [CFSG.KC.Fi23K.wv_cons, CFSG.KC.Fi23K.wv_nil] at h
  exact h.symm

theorem acts_dWord7 :
    ActsAs (phiX (dWord.map fun x => if x = 0 then wα else wβ).prod ^ 7) (tb G 43) := by
  intro x hx
  rw [acts_pow acts_dWord 7 x hx]
  have h := eqv (k := 137) (by norm_num) hx
  rw [eq137.1, eq137.2] at h
  simp only [CFSG.KC.Fi23K.wv_cons, CFSG.KC.Fi23K.wv_nil] at h
  exact h.symm

theorem dTable_ap {m : ℕ} (hm : m < 31671) : ap (dTable orbLit) m = tb G 43 m := by
  have h := (rep_dWord dWord).powT (by norm_num) 7 m hm
  change ap (powT 31671 7 (dWordTable orbLit)) m = _
  unfold dWordTable
  rw [h, idx_of_lt _ hm, Equiv.Perm.smul_def, acts_dWord7 m hm]

theorem bi_ap {m : ℕ} (hm : m < 31671) : ap (genTables orbLit (-2)) m = tb G 41 m := by
  have h := ((genTables_TR (z := -2) (by decide) (by decide)).2 m hm).1
  rw [h]
  rfl

theorem treeAct_cp : ∀ k < 31671, ∀ m (hm : m < 31671),
    treeAct orbLit.par orbLit.lab orbLit.alpha orbLit.beta (dTable orbLit) (genTables orbLit (-2))
      k m = (cp k ⟨m, hm⟩).val := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk m hm
    rw [treeAct.eq_def]
    by_cases h0 : k = 0
    · subst h0
      rw [dite_eq_right (by omega), dTable_ap hm, cp_zero]
      exact (phiX_wD m hm).symm
    · have hp := (tr_pt hk h0).1
      have epar : ap orbLit.par k = tb G 91 k := ap_tabOf 91 hk
      have elb : ap orbLit.lab k = tb G 92 k := ap_tabOf 92 hk
      have ea : ∀ x < 31671, ap orbLit.alpha x = tb G 39 x := fun x hx => ap_tabOf 39 hx
      have eb : ∀ x < 31671, ap orbLit.beta x = tb G 40 x := fun x hx => ap_tabOf 40 hx
      rw [dite_eq_left ⟨Nat.pos_of_ne_zero h0, by rw [epar]; exact hp⟩, epar, elb]
      by_cases hl : tb G 92 k = 1
      · have hb : (tb G 92 k == 1) = true := by rw [hl]; rfl
        rw [if_pos hb, cp_step_a hk h0 hl hm, ea m hm,
          ih _ hp (by omega) _ (rng 39 (by norm_num) m hm), ea _ (Fin.isLt _)]
      · have hb : (tb G 92 k == 1) = false := Bool.eq_false_iff.2 fun e => hl (beq_iff_eq.1 e)
        rw [if_neg (by rw [hb]; decide), cp_step_b hk h0 hl hm, bi_ap hm,
          ih _ hp (by omega) _ (rng 41 (by norm_num) m hm), eb _ (Fin.isLt _)]

end

theorem gs6_card : Nat.card (Gs T23 (bF hn BB) 6) = 1 := by
  have hc := card_chain T23 (bF hn BB) 6
  have hT : Nat.card T23 = 4089470473293004800 := by rw [grp_eq]; exact card_Xc_eq
  have hle : ((List.range 6).map CNT).prod ≤
      ∏ l ∈ Finset.range 6, (MulAction.orbit (Gs T23 (bF hn BB) l) (bF hn BB l)).ncard := by
    rw [prod_range_map]
    refine Finset.prod_le_prod' fun l hl => ?_
    have hl' := Finset.mem_range.1 hl
    rw [← dSet_card chain_hyp hn hl', ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (dSet_sub_orbit chain_hyp hn hl') (Set.toFinite _)
  rw [prod_cnt] at hle
  rw [hT] at hc
  have hpos : 0 < Nat.card (Gs T23 (bF hn BB) 6) := Nat.card_pos
  by_contra hne
  have h2 : 2 ≤ Nat.card (Gs T23 (bF hn BB) 6) := by omega
  have := Nat.mul_le_mul hle h2
  omega

theorem fix_base {p : Equiv.Perm (Fin 31671)} (hp : p ∈ Xc)
    (hfix : ∀ k (hk : k < 6), (p ⟨k, by omega⟩).val = k) : p = 1 := by
  have hmem : p ∈ Gs T23 (bF hn BB) 6 := by
    rw [mem_Gs]
    refine ⟨by rw [grp_eq]; exact hp, fun k hk => Fin.ext ?_⟩
    have e : bF hn BB k = ⟨k, by omega⟩ := Fin.ext (bF_val chain_hyp hn hk)
    rw [e, hfix k hk]
  rw [((Subgroup.card_le_one_iff_eq_bot _).1 (le_of_eq gs6_card))] at hmem
  exact Subgroup.mem_bot.1 hmem

end CertificateChecks.KernelFi23C

end
