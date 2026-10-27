module

public import Certificates.Kernel.Fi23R.Sound
public import Certificates.Data.CFSGNative.Fi23.Classes
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23R

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23R CFSG.KS.Raw.Orb
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M
  CFSG.KS.PC CFSG.KS.PCC

abbrev Pt := Equiv.Perm (Fin 31671)

@[expose] noncomputable def aP : Pt := phiX wα
@[expose] noncomputable def bP : Pt := phiX wβ
@[expose] noncomputable def dP : Pt := phiX wD
@[expose] noncomputable def cT (k : ℕ) : Pt := phiX (tk k * wD * (tk k)⁻¹)

@[expose] noncomputable def lp (c : ℕ) : Pt :=
  if c = 39 then aP else if c = 40 then bP else if c = 41 then bP⁻¹ else if c < 128 then dP
  else cT (c - 128)

@[expose] def okL (c : ℕ) : Prop := c = 39 ∨ c = 40 ∨ c = 41 ∨ c = 43 ∨ (128 ≤ c ∧ c < 31799)

instance (c : ℕ) : Decidable (okL c) :=
  inferInstanceAs (Decidable (c = 39 ∨ c = 40 ∨ c = 41 ∨ c = 43 ∨ (128 ≤ c ∧ c < 31799)))

@[expose] noncomputable def wp : List ℕ → Pt
  | [] => 1
  | c :: w => wp w * lp c

theorem actsAs_congr {p : Pt} {f g : ℕ → ℕ} (h : ActsAs p f) (hfg : ∀ x < 31671, f x = g x) :
    ActsAs p g := fun x hx => by rw [h x hx, hfg x hx]

theorem phiX_mem' (h : PG) : phiX h ∈ Xc := by
  rw [← range_phiX]
  exact ⟨h, rfl⟩

theorem cT_mem (k : ℕ) : cT k ∈ Xc := phiX_mem' _

theorem lp_39 : lp 39 = aP := by unfold lp; simp
theorem lp_40 : lp 40 = bP := by unfold lp; simp
theorem lp_41 : lp 41 = bP⁻¹ := by unfold lp; simp
theorem lp_43 : lp 43 = dP := by unfold lp; simp

theorem lp_big {c : ℕ} (hc : 128 ≤ c) : lp c = cT (c - 128) := by
  unfold lp
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem lp_mem (c : ℕ) : lp c ∈ Xc := by
  unfold lp
  split_ifs
  · exact phiX_mem' _
  · exact phiX_mem' _
  · exact Subgroup.inv_mem _ (phiX_mem' _)
  · exact phiX_mem' _
  · exact cT_mem _

theorem wp_nil : wp [] = 1 := rfl

theorem wp_cons (c : ℕ) (w : List ℕ) : wp (c :: w) = wp w * lp c := rfl

theorem wp_append : ∀ u v : List ℕ, wp (u ++ v) = wp v * wp u
  | [], v => by rw [List.nil_append, wp_nil, mul_one]
  | c :: u, v => by rw [List.cons_append, wp_cons, wp_append u v, wp_cons, mul_assoc]

theorem wp_mem : ∀ w : List ℕ, wp w ∈ Xc
  | [] => Subgroup.one_mem _
  | c :: w => Subgroup.mul_mem _ (wp_mem w) (lp_mem c)

theorem wp_powW (w : List ℕ) : ∀ e : ℕ, wp (CFSG.KC.Fi23R.powW e w) = wp w ^ e
  | 0 => rfl
  | e + 1 => by
    have h : CFSG.KC.Fi23R.powW (e + 1) w = w ++ CFSG.KC.Fi23R.powW e w := by
      unfold CFSG.KC.Fi23R.powW
      rw [List.replicate_succ, List.flatten_cons]
    rw [h, wp_append, wp_powW w e, pow_succ]

theorem wp_rev_map (f : ℤ → ℕ) : ∀ w : List ℤ,
    wp ((w.reverse).map f) = (w.map fun z => lp (f z)).prod
  | [] => rfl
  | z :: w => by
    rw [List.reverse_cons, List.map_append, wp_append, wp_rev_map f w]
    simp only [List.map_cons, List.map_nil, List.prod_cons, wp_cons, wp_nil, one_mul]

theorem okL_invL {c : ℕ} (hc : okL c) : okL (invL c) := by
  unfold invL
  split_ifs with h1 h2
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)
  · exact hc

theorem ok_append {u v : List ℕ} (hu : ∀ c ∈ u, okL c) (hv : ∀ c ∈ v, okL c) :
    ∀ c ∈ u ++ v, okL c := fun c hc => (List.mem_append.1 hc).elim (hu c) (hv c)

theorem ok_invW {w : List ℕ} (hw : ∀ c ∈ w, okL c) : ∀ c ∈ invW w, okL c := by
  intro c hc
  unfold invW at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hc)
  exact okL_invL (hw d hd)

theorem ok_powW {w : List ℕ} (hw : ∀ c ∈ w, okL c) (e : ℕ) :
    ∀ c ∈ CFSG.KC.Fi23R.powW e w, okL c := by
  intro c hc
  unfold CFSG.KC.Fi23R.powW at hc
  obtain ⟨l, hl, hc⟩ := List.mem_flatten.1 hc
  rw [List.eq_of_mem_replicate hl] at hc
  exact hw c hc

theorem ok_brayW {wR wG : List ℕ} (hR : ∀ c ∈ wR, okL c) (hG : ∀ c ∈ wG, okL c) (e : ℕ)
    (odd : Bool) : ∀ c ∈ brayW wR wG e odd, okL c := by
  have hp := ok_powW (ok_append (ok_append (ok_append hG hR) (ok_invW hG)) hR) e
  unfold brayW
  cases odd
  · exact hp
  · exact ok_append hp hG

theorem ok_commW {wX wY : List ℕ} (hX : ∀ c ∈ wX, okL c) (hY : ∀ c ∈ wY, okL c) :
    ∀ c ∈ commW wX wY, okL c := by
  unfold commW
  exact ok_append (ok_append (ok_append (ok_invW hY) (ok_invW hX)) hY) hX

section


theorem aP_acts : ActsAs aP (tb G 39) := phiX_wα
theorem bP_acts : ActsAs bP (tb G 40) := phiX_wβ
theorem dP_acts : ActsAs dP (tb G 43) := phiX_wD

theorem bPi_acts : ActsAs bP⁻¹ (tb G 41) :=
  bP_acts.inv (rng 41 (by norm_num)) fun _ hx => binv_right hx

theorem aP_inv : aP⁻¹ = aP :=
  (aP_acts.inv (rng 39 (by norm_num)) fun _ hx => (ord_pt hx).1).ext aP_acts

theorem base_one {p : Pt} (hp : p ∈ Xc) (hb : ∀ i (hi : i < 6), (p ⟨i, by omega⟩).val = i) :
    p = 1 := by
  have hc := card_chain T23 (bF hn BB) 6
  have hT : Nat.card T23 = 4089470473293004800 := by rw [grp_eq]; exact card_Xc_eq
  have hge : ∏ l ∈ Finset.range 6, CNT l ≤
      ∏ l ∈ Finset.range 6, (MulAction.orbit (Gs T23 (bF hn BB) l) (bF hn BB l)).ncard := by
    refine Finset.prod_le_prod' fun l hl => ?_
    have hl' := Finset.mem_range.1 hl
    rw [← dSet_card chain_hyp hn hl', ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (dSet_sub_orbit chain_hyp hn hl') (Set.toFinite _)
  have hp6 : ∏ l ∈ Finset.range 6, CNT l = 4089470473293004800 := by
    rw [← prod_range_map]
    exact prod_cnt
  have hc' : (∏ l ∈ Finset.range 6, (MulAction.orbit (Gs T23 (bF hn BB) l) (bF hn BB l)).ncard) *
      Nat.card (Gs T23 (bF hn BB) 6) = 4089470473293004800 := by rw [← hc, hT]
  have hge' : 4089470473293004800 ≤
      ∏ l ∈ Finset.range 6, (MulAction.orbit (Gs T23 (bF hn BB) l) (bF hn BB l)).ncard :=
    hp6 ▸ hge
  have hcard : Nat.card (Gs T23 (bF hn BB) 6) ≤ 1 := by
    by_contra h
    have h2 : 4089470473293004800 * 2 ≤
        (∏ l ∈ Finset.range 6, (MulAction.orbit (Gs T23 (bF hn BB) l) (bF hn BB l)).ncard) *
          Nat.card (Gs T23 (bF hn BB) 6) := Nat.mul_le_mul hge' (by omega)
    omega
  have hmem : p ∈ Gs T23 (bF hn BB) 6 := by
    refine (mem_Gs 6 p).2 ⟨by rw [grp_eq]; exact hp, fun k hk => ?_⟩
    have e : bF hn BB k = ⟨k, by omega⟩ := Fin.ext (bF_val chain_hyp hn hk)
    rw [e]
    exact Fin.ext (hb k hk)
  rw [Subgroup.eq_bot_of_card_le _ hcard] at hmem
  exact (Subgroup.mem_bot).1 hmem

theorem base_eq {p q : Pt} (hp : p ∈ Xc) (hq : q ∈ Xc)
    (hb : ∀ i (hi : i < 6), (p ⟨i, by omega⟩).val = (q ⟨i, by omega⟩).val) : p = q := by
  have h := base_one (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq) hp) fun i hi => by
    rw [Equiv.Perm.mul_apply]
    have e : p ⟨i, by omega⟩ = q ⟨i, by omega⟩ := Fin.ext (hb i hi)
    rw [e]
    simp
  exact (inv_mul_eq_one.1 h).symm

theorem cT_zero : cT 0 = dP := by
  have e := conj_eq (v := tk 0) (g := 1) (by rw [tk_pt (by norm_num), map_one]; rfl)
  unfold cT dP
  rw [e, one_mul, inv_one, mul_one]

theorem cT_step {k : ℕ} (hk : k < 31671) (hk0 : k ≠ 0) :
    cT k = if tb G 92 k = 1 then aP * cT (tb G 91 k) * aP⁻¹
      else bP * cT (tb G 91 k) * bP⁻¹ := by
  obtain ⟨hp, hA, hB⟩ := tr_pt hk hk0
  have hpN : tb G 91 k < 31671 := by omega
  split_ifs with hl
  · have e := conj_eq (v := tk k) (g := wα * tk (tb G 91 k)) (by
      rw [tk_pt hk, map_mul, Equiv.Perm.mul_apply, tk_pt hpN]
      exact Fin.ext (by rw [phiX_wα _ hpN, hA hl]))
    have e2 : wα * tk (tb G 91 k) * wD * (wα * tk (tb G 91 k))⁻¹ =
        wα * (tk (tb G 91 k) * wD * (tk (tb G 91 k))⁻¹) * wα⁻¹ := by group
    unfold cT aP
    rw [e, e2]
    simp only [map_mul, map_inv]
  · have e := conj_eq (v := tk k) (g := wβ * tk (tb G 91 k)) (by
      rw [tk_pt hk, map_mul, Equiv.Perm.mul_apply, tk_pt hpN]
      exact Fin.ext (by rw [phiX_wβ _ hpN, hB hl]))
    have e2 : wβ * tk (tb G 91 k) * wD * (wβ * tk (tb G 91 k))⁻¹ =
        wβ * (tk (tb G 91 k) * wD * (tk (tb G 91 k))⁻¹) * wβ⁻¹ := by group
    unfold cT bP
    rw [e, e2]
    simp only [map_mul, map_inv]

theorem cT_acts_f : ∀ f k, k < 31671 → tb G 93 k < f → ActsAs (cT k) (tAf G f k)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, k, hk, hd => by
    by_cases h0 : k = 0
    · subst h0
      rw [cT_zero]
      exact actsAs_congr dP_acts fun x _ => by rw [tAf_succ, if_pos rfl]
    · obtain ⟨hp, -, -⟩ := tr_pt hk h0
      have hpN : tb G 91 k < 31671 := by omega
      have hdp : tb G 93 (tb G 91 k) < f := by
        have := (dep_pt hk).2 h0
        omega
      have ih := cT_acts_f f _ hpN hdp
      rw [cT_step hk h0]
      split_ifs with hl
      · have hi : ActsAs aP⁻¹ (tb G 39) := by rw [aP_inv]; exact aP_acts
        refine actsAs_congr ((aP_acts.mul ih).mul hi) fun x _ => ?_
        rw [tAf_succ, if_neg h0, if_pos hl]
      · refine actsAs_congr ((bP_acts.mul ih).mul bPi_acts) fun x _ => ?_
        rw [tAf_succ, if_neg h0, if_neg hl]

theorem cT_acts {k : ℕ} (hk : k < 31671) : ActsAs (cT k) (tA G k) :=
  cT_acts_f 200 k hk (dep_pt hk).1

theorem cT_conj (h : PG) {k : ℕ} (hk : k < 31671) :
    phiX h * cT k * (phiX h)⁻¹ = cT (phiX h ⟨k, hk⟩).val := by
  have hk' := (phiX h ⟨k, hk⟩).isLt
  have e := conj_eq (v := h * tk k) (g := tk (phiX h ⟨k, hk⟩).val) (by
    rw [map_mul, Equiv.Perm.mul_apply, tk_pt hk, tk_pt hk'])
  have e2 : h * tk k * wD * (h * tk k)⁻¹ = h * (tk k * wD * (tk k)⁻¹) * h⁻¹ := by group
  unfold cT
  rw [← e, e2]
  simp only [map_mul, map_inv]

theorem dP_inv (hD : dP * dP = 1) : dP⁻¹ = dP := inv_eq_of_mul_eq_one_right hD

theorem cT_inv (hD : dP * dP = 1) (k : ℕ) : (cT k)⁻¹ = cT k := by
  have hDi : (phiX wD)⁻¹ = phiX wD := dP_inv hD
  unfold cT
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv, hDi, mul_assoc]

theorem lp_acts {c : ℕ} (hc : okL c) : ActsAs (lp c) (lf G c) := by
  rcases hc with rfl | rfl | rfl | rfl | ⟨h1, h2⟩
  · rw [lp_39]
    exact actsAs_congr aP_acts fun x _ => by rw [lf_eq, if_pos (by norm_num)]
  · rw [lp_40]
    exact actsAs_congr bP_acts fun x _ => by rw [lf_eq, if_pos (by norm_num)]
  · rw [lp_41]
    exact actsAs_congr bPi_acts fun x _ => by rw [lf_eq, if_pos (by norm_num)]
  · rw [lp_43]
    exact actsAs_congr dP_acts fun x _ => by rw [lf_eq, if_pos (by norm_num)]
  · rw [lp_big h1]
    exact actsAs_congr (cT_acts (by omega)) fun x _ => by rw [lf_eq, if_neg (by omega)]

theorem wp_acts : ∀ w : List ℕ, (∀ c ∈ w, okL c) → ActsAs (wp w) (wa G w)
  | [], _ => fun _ _ => rfl
  | c :: w, h => by
    have h1 := lp_acts (h c List.mem_cons_self)
    have h2 := wp_acts w fun d hd => h d (List.mem_cons_of_mem c hd)
    rw [wp_cons]
    exact actsAs_congr (h2.mul h1) fun x _ => (wa_cons c w x).symm

theorem wp_eq_of_eqB {u v : List ℕ} (h : eqB G u v = true) (hu : ∀ c ∈ u, okL c)
    (hv : ∀ c ∈ v, okL c) : wp u = wp v :=
  base_eq (wp_mem u) (wp_mem v) fun i hi => by
    rw [wp_acts u hu i (by omega), wp_acts v hv i (by omega)]
    exact eqB_spec h i hi

theorem lp_invL (hD : dP * dP = 1) {c : ℕ} (hc : okL c) : lp (invL c) = (lp c)⁻¹ := by
  rcases hc with rfl | rfl | rfl | rfl | ⟨h1, h2⟩
  · have e : invL 39 = 39 := rfl
    rw [e, lp_39, aP_inv]
  · have e : invL 40 = 41 := rfl
    rw [e, lp_40, lp_41]
  · have e : invL 41 = 40 := rfl
    rw [e, lp_40, lp_41, inv_inv]
  · have e : invL 43 = 43 := rfl
    rw [e, lp_43, dP_inv hD]
  · have e : invL c = c := by unfold invL; rw [if_neg (by omega), if_neg (by omega)]
    rw [e, lp_big h1, cT_inv hD]

theorem wp_invW (hD : dP * dP = 1) : ∀ w : List ℕ, (∀ c ∈ w, okL c) → wp (invW w) = (wp w)⁻¹
  | [], _ => by rw [show invW [] = [] from rfl, wp_nil, inv_one]
  | c :: w, h => by
    have e : invW (c :: w) = invW w ++ [invL c] := by
      unfold invW
      rw [List.map_cons, List.reverse_cons]
    rw [e, wp_append, wp_cons, wp_nil, one_mul,
      wp_invW hD w fun d hd => h d (List.mem_cons_of_mem c hd),
      lp_invL hD (h c List.mem_cons_self), wp_cons, mul_inv_rev]

@[expose] def RW (T : Table) (w : List ℕ) : Prop :=
  T.size = 31671 ∧ (∀ c ∈ w, okL c) ∧ Rep 31671 T (wp w)

theorem idx_eq (p : Pt) {i : ℕ} (hi : i < 31671) : idx 31671 p i = (p ⟨i, hi⟩).val := by
  rw [idx_of_lt _ hi, Equiv.Perm.smul_def]

theorem RW.ap {T : Table} {w : List ℕ} (h : RW T w) {i : ℕ} (hi : i < 31671) :
    CFSG.Sporadic.Th.Native.ap T i = wa G w i := by
  rw [h.2.2 i hi, idx_eq _ hi, wp_acts w h.2.1 i hi]

theorem RW.word {T : Table} {u v : List ℕ} (h : RW T u) (e : u = v) : RW T v := e ▸ h

theorem RW.congr {T : Table} {u v : List ℕ} (h : RW T u) (hv : ∀ c ∈ v, okL c)
    (e : wp u = wp v) : RW T v := ⟨h.1, hv, e ▸ h.2.2⟩

theorem rw_of_acts {T : Table} {w : List ℕ} (hs : T.size = 31671) (hw : ∀ c ∈ w, okL c)
    (h : ∀ i < 31671, CFSG.Sporadic.Th.Native.ap T i = wa G w i) : RW T w :=
  ⟨hs, hw, fun i hi => by rw [h i hi, idx_eq _ hi, wp_acts w hw i hi]⟩

theorem compT_size (P Q : Table) : (compT 31671 P Q).size = 31671 := by
  unfold compT
  exact Array.size_ofFn

theorem idT_size : (idT 31671).size = 31671 := by
  unfold idT
  exact Array.size_ofFn

theorem powT_size (P : Table) : ∀ e, (powT 31671 e P).size = 31671
  | 0 => idT_size
  | _ + 1 => compT_size _ _

theorem rw_compT {P Q : Table} {u v : List ℕ} (hP : RW P u) (hQ : RW Q v) :
    RW (compT 31671 P Q) (v ++ u) :=
  ⟨compT_size P Q, ok_append hQ.2.1 hP.2.1, by rw [wp_append]; exact Rep.compT hP.2.2 hQ.2.2⟩

theorem rw_powT {P : Table} {u : List ℕ} (h : RW P u) (e : ℕ) :
    RW (powT 31671 e P) (CFSG.KC.Fi23R.powW e u) :=
  ⟨powT_size P e, ok_powW h.2.1 e, by rw [wp_powW]; exact Rep.powT (by norm_num) h.2.2 e⟩

theorem rw_idT : RW (idT 31671) [] :=
  ⟨idT_size, fun _ h => absurd h List.not_mem_nil, Rep.idT (by norm_num)⟩

theorem RW.tr {P : Table} {u : List ℕ} (h : RW P u) : CFSG.KS.TW.TR 31671 P (wa G u) :=
  ⟨h.1, fun i hi => ⟨h.ap hi, by rw [← wp_acts u h.2.1 i hi]; exact (wp u ⟨i, hi⟩).isLt⟩⟩

theorem inv_pt (hD : dP * dP = 1) {u : List ℕ} (hu : ∀ c ∈ u, okL c) {i : ℕ} (hi : i < 31671) :
    wa G (invW u) (wa G u i) = i ∧ wa G u (wa G (invW u) i) = i := by
  have ha := wp_acts u hu
  have hb := wp_acts (invW u) (ok_invW hu)
  have e1 : ∀ (p : Pt) (j : Fin 31671), (⟨(p j).val, (p j).isLt⟩ : Fin 31671) = p j :=
    fun _ _ => rfl
  constructor
  · rw [← ha i hi, ← hb _ (wp u ⟨i, hi⟩).isLt, e1, wp_invW hD u hu]
    simp
  · rw [← hb i hi, ← ha _ (wp (invW u) ⟨i, hi⟩).isLt, e1, wp_invW hD u hu]
    simp

theorem rw_invT (hD : dP * dP = 1) {P : Table} {u : List ℕ} (h : RW P u) :
    RW (invT 31671 P) (invW u) := by
  have hi := ok_invW h.2.1
  have hT := CFSG.KS.TW.invT_TR (by norm_num) h.tr (g := wa G (invW u)) fun i hi' => by
    refine ⟨?_, (inv_pt hD h.2.1 hi').2, (inv_pt hD h.2.1 hi').1⟩
    rw [← wp_acts (invW u) hi i hi']
    exact (wp (invW u) ⟨i, hi'⟩).isLt
  exact rw_of_acts hT.1 hi fun i hi' => (hT.2 i hi').1

theorem rw_invOK (hD : dP * dP = 1) {P : Table} {u : List ℕ} (h : RW P u) :
    invOK 31671 P (invT 31671 P) = true :=
  CFSG.KS.TW.invOK_of h.tr (rw_invT hD h).tr fun _ hi => (inv_pt hD h.2.1 hi).1

theorem RW.beq {A B : Table} {u v : List ℕ} (hA : RW A u) (hB : RW B v) (e : wp u = wp v) :
    (A == B) = true := by
  rw [beq_iff_eq]
  apply Array.ext (by rw [hA.1, hB.1])
  intro i h1 h2
  have hi : i < 31671 := by rw [← hA.1]; exact h1
  have ea := hA.2.2 i hi
  have eb := hB.2.2 i hi
  rw [e, ← eb] at ea
  unfold CFSG.Sporadic.Th.Native.ap at ea
  rw [getElem!_pos A i h1, getElem!_pos B i h2] at ea
  exact UInt32.toNat_inj.1 ea

theorem RW.isIdT_false {T : Table} {w : List ℕ} (h : RW T w) (hm : wa G w 2 ≠ 2) :
    isIdT T = false := by
  unfold isIdT
  cases e : allIn 0 31671 fun i => CFSG.Sporadic.Th.Native.ap T i == i
  · rfl
  · have := (allIn_eq_true.1 e) 2 (Nat.zero_le _) (by norm_num)
    rw [beq_iff_eq, h.ap (by norm_num)] at this
    exact absurd this hm

theorem RW.countP {T : Table} {w : List ℕ} (h : RW T w) :
    (List.range 31671).countP (fun i => CFSG.Sporadic.Th.Native.ap T i == i) =
      (List.range 31671).countP (fxW G w) := by
  apply List.countP_congr
  intro i hi
  rw [beq_iff_eq, h.ap (List.mem_range.1 hi), fxW_iff]

theorem regZ_ok {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    regZ z = 39 ∨ regZ z = 40 ∨ regZ z = 41 := by
  rcases hz with rfl | rfl | rfl | rfl <;> decide

theorem okL_regZ {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) : okL (regZ z) := by
  rcases regZ_ok hz with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem rep_gen {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    Rep 31671 (genTables orbLit z) (lp (regZ z)) := by
  have hT := genTables_TR (z := z) (by omega) (by omega)
  intro i hi
  rw [(hT.2 i hi).1, idx_eq _ hi, lp_acts (okL_regZ hz) i hi, lf_eq,
    if_pos (by rcases regZ_ok hz with h | h | h <;> omega)]

theorem rw_genTables {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    RW (genTables orbLit z) [regZ z] := by
  have hT := genTables_TR (z := z) (by omega) (by omega)
  refine ⟨hT.1, fun c hc => ?_, ?_⟩
  · rw [List.mem_singleton] at hc
    rw [hc]
    exact okL_regZ hz
  · rw [wp_cons, wp_nil, one_mul]
    exact rep_gen hz

theorem rw_wordT (w : List ℤ) (hw : ∀ z ∈ w, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    RW (CFSG.Sporadic.Th.Native.wordT 31671 (genTables orbLit) w) ((w.reverse).map regZ) := by
  refine ⟨wordT_size 31671 _ w, fun c hc => ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hc
    exact okL_regZ (hw z (List.mem_reverse.1 hz))
  · rw [wp_rev_map]
    exact Rep.wordT (by norm_num) w fun l hl => rep_gen (hw l hl)

theorem dLetters_ok : ∀ z ∈ dLetters (), z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by
  intro z hz
  unfold dLetters at hz
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hz
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem wa_rev_wv : ∀ L : List ℕ, (∀ c ∈ L, c < 128) → ∀ x, wa G L.reverse x = wv G L x
  | [], _, _ => rfl
  | c :: L, h, x => by
    rw [List.reverse_cons, wa_append, wa_rev_wv L (fun d hd => h d (List.mem_cons_of_mem c hd)) x,
      wa_cons, wa_nil, lf_eq, if_pos (h c List.mem_cons_self), wv_cons]

theorem rw_dTab : RW (dTab orbLit) [43] := by
  have h := rw_powT (rw_wordT (dLetters ()) dLetters_ok) 7
  refine h.congr (fun c hc => by
    rw [List.mem_singleton] at hc
    exact Or.inr (Or.inr (Or.inr (Or.inl hc)))) ?_
  rw [wp_powW, wp_cons, wp_nil, one_mul, lp_43]
  have eW : (dLetters ()).reverse.map regZ = (dWord.map fun x => if x = 0 then 39 else 40).reverse := by
    rw [List.map_reverse]
    congr 1
  have hl : ∀ c ∈ dWord.map (fun x => if x = 0 then 39 else 40), c < 128 := by
    intro c hc
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc
    split_ifs <;> norm_num
  have hZ : ActsAs (wp ((dLetters ()).reverse.map regZ)) (tb G 42) := by
    refine actsAs_congr (wp_acts _ (rw_wordT (dLetters ()) dLetters_ok).2.1) fun x hx => ?_
    rw [eW, wa_rev_wv _ hl x]
    have h := eqv (k := 136) (by norm_num) hx
    rw [eq136.1, eq136.2, wv_cons, wv_nil] at h
    exact h.symm
  have h7 : ActsAs (wp ((dLetters ()).reverse.map regZ) ^ 7) (tb G 43) := by
    refine actsAs_congr (acts_pow hZ 7) fun x hx => ?_
    have h := eqv (k := 137) (by norm_num) hx
    rw [eq137.1, eq137.2, wv_cons, wv_nil] at h
    exact h.symm
  exact h7.ext dP_acts

theorem rw_treeActTab {k : ℕ} (hk : k < 31671) :
    RW (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) k) [128 + k] := by
  have hD := rw_dTab
  have hbi := genTables_TR (z := -2) (by norm_num) (by norm_num)
  have hok : ∀ c ∈ [128 + k], okL c := fun c hc => by
    rw [List.mem_singleton] at hc
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  refine rw_of_acts (by unfold treeActTab; exact Array.size_ofFn) hok fun m hm => ?_
  unfold treeActTab
  rw [ap_ofFn _ hm, UInt32.toNat_ofNat',
    tAf_treeAct (fun m hm => by rw [hD.ap hm, wa_cons, wa_nil, lf_eq, if_pos (by norm_num)])
      (fun m hm => (hbi.2 m hm).1) 200 k hk (dep_pt hk).1 m hm,
    Nat.mod_eq_of_lt (lt_trans (tAf_lt 200 k m hm) (by norm_num)), wa_cons, wa_nil, lf_eq,
    if_neg (by omega), Nat.add_sub_cancel_left]
  rfl

end

end CertificateChecks.KernelFi23R

end
