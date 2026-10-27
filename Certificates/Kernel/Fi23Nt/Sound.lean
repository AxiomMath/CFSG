module

public import Certificates.Data.Kernel.Fi23Nt.Defs
public import Certificates.Data.Kernel.Fi23Nt.FixDefs
public import Certificates.Data.Kernel.Fi23Nt.MiscDefs
public import Certificates.Data.Kernel.Fi23Nt.FixQDefs
public import Certificates.Kernel.Fi23Q.Regs
public import CFSG.Certificates.Kernel.Fi23Nt.TabSound
public import CFSG.Certificates.Kernel.Fi23Nt.Math

public section

namespace CertificateChecks.KernelFi23Nt

open CFSG.Sporadic.Fi23 CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.KC.Fi23Nt
  CFSG.KC.Fi23R CertificateChecks.KernelFi23Q CFSG.KS.Fi23Nt CFSG.KS.E27Lie
  CFSG.HardMathSupport.Foote.E27 CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base)


noncomputable abbrev wE (w : List ℕ) : CFSG.Sporadic.Fi23.J := (w.map regE).prod

abbrev WOK (w : List ℕ) : Prop := ∀ r ∈ w, RegOK r

theorem wv_eq {w : List ℕ} (hw : WOK w) {x : ℕ} (hx : x < 31671) :
    wv G w x = idx 31671 (wE w) x :=
  wvG_eq w hw x hx

theorem tA_eq {k m : ℕ} (hk : k < 31671) (hm : m < 31671) : tA G k m = idx 31671 (conjPt k) m :=
  (conjPt_acts hk m hm).symm

theorem idx_inv_cancel (u : CFSG.Sporadic.Fi23.J) {y : ℕ} : idx 31671 u⁻¹ (idx 31671 u y) = y := by
  rw [← idx_mul, inv_mul_cancel, idx_one]

theorem relK_spec {POS PAR LAB : ℕ → ℕ} (hD : ∀ y < 31671, tb G 43 y = idx 31671 d y)
    {v x : ℕ} (hx : x < 31671) {u : CFSG.Sporadic.Fi23.J} (hu : idx 31671 u 0 = v)
    (hc : climb0 PAR LAB G 20 (POS v) x = idx 31671 u⁻¹ x) :
    relK POS PAR LAB G v x = true ↔ conjPt v * conjPt x = conjPt x * conjPt v := by
  unfold relK
  rw [sB_eq, hc, hD _ (idx_lt _ hx), Nat.beq_eq]
  have hv : conjPt v = u * d * u⁻¹ := by
    rw [← hu, ← conjPt_idx u (by norm_num), conjPt_zero]
  have e := mem_centralizer_conjPt_iff (conjPt v) hx
  rw [Subgroup.mem_centralizer_singleton_iff] at e
  rw [e, hv, idx_mul, idx_mul]
  constructor
  · intro h
    rw [h, ← idx_mul, mul_inv_cancel, idx_one]
  · intro h
    have h' := congrArg (idx 31671 u⁻¹) h
    rwa [idx_inv_cancel] at h'

theorem not_xor_iff (a b : Bool) : Bool.not (Bool.xor a b) = true ↔ a = b := by
  cases a <;> cases b <;> simp

theorem passK_spec {POS PAR LAB : ℕ → ℕ} :
    ∀ (S : List (List ℕ × Bool)) (v : ℕ),
      passK POS PAR LAB G S v = true ↔ ∀ s ∈ S, relK POS PAR LAB G v (wv G s.1 v) = s.2
  | [], v => by simp [passK]
  | s :: S, v => by
    change Bool.rec (motive := fun _ => Bool) false (passK POS PAR LAB G S v)
      (Bool.not (Bool.xor (relK POS PAR LAB G v (wv G s.1 v)) s.2)) = true ↔ _
    rw [CFSG.KS.bAnd_iff, not_xor_iff, passK_spec S v, List.forall_mem_cons]

theorem foldCntB (b : ℕ) (c : ℕ → Bool) : ∀ len s : ℕ,
    foldBlk b (fun v s => nIf(c v, Nat.succ s, s)) len s =
      s + ((Finset.range len).filter fun l => c (b + l) = true).card
  | 0, s => by simp [foldBlk]
  | len + 1, s => by
    change strictN (nIf(c (Nat.add b len), Nat.succ s, s))
      (foldBlk b (fun v s => nIf(c v, Nat.succ s, s)) len) = _
    have e0 : Nat.add b len = b + len := rfl
    rw [sN_eq, foldCntB b c len, Finset.range_add_one, Finset.filter_insert, e0, nRec_eq]
    by_cases hc : c (b + len) = true
    · rw [if_pos hc, if_pos hc, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [if_neg hc, if_neg hc]

theorem cnt_spec {POS PAR LAB : ℕ → ℕ} {S : List (List ℕ × Bool)} {lo len c : ℕ}
    (h : cntSlK POS PAR LAB G S lo len c = true) :
    ((Finset.range len).filter fun l => passK POS PAR LAB G S (lo + l) = true).card = c := by
  have e := beq_of h
  unfold cntK at e
  rw [foldCntB, Nat.zero_add] at e
  exact e

theorem memK_spec : ∀ {F : List ℕ} {v : ℕ}, memK F v = true → v ∈ F
  | [], _, h => absurd h (by simp [memK])
  | p :: F, v, h => by
    change Bool.rec (motive := fun _ => Bool) (memK F v) true (Nat.beq p v) = true at h
    rw [bRec_eq] at h
    by_cases hp : Nat.beq p v = true
    · rw [beq_of hp]
      exact List.mem_cons_self
    · rw [if_neg hp] at h
      exact List.mem_cons_of_mem p (memK_spec h)

theorem movK_spec : ∀ {W : List (List ℕ)} {v : ℕ}, movK G W v = true → ∃ w ∈ W, wv G w v ≠ v
  | [], _, h => absurd h (by simp [movK])
  | w :: W, v, h => by
    change Bool.rec (motive := fun _ => Bool) true (movK G W v) (Nat.beq (wv G w v) v) = true at h
    rw [bRec_eq] at h
    by_cases hw : Nat.beq (wv G w v) v = true
    · rw [if_pos hw] at h
      obtain ⟨w', hw', e⟩ := movK_spec h
      exact ⟨w', List.mem_cons_of_mem w hw', e⟩
    · exact ⟨w, List.mem_cons_self, fun e => hw (beq_true e)⟩

theorem fix_spec {F : List ℕ} {W : List (List ℕ)} (hW : ∀ w ∈ W, WOK w) {lo len : ℕ}
    (h : fixSlK G F W lo len = true) {v : ℕ} (hv1 : lo ≤ v) (hv2 : v < lo + len)
    (hv : v < 31671) (hfix : ∀ w ∈ W, idx 31671 (wE w) v = v) : v ∈ F := by
  have h1 := CFSG.KS.allBlk_spec h (v - lo) (by omega)
  have e : Nat.add lo (v - lo) = v := by
    change lo + (v - lo) = v
    omega
  rw [e, bRec_eq] at h1
  by_cases hm : memK F v = true
  · exact memK_spec hm
  · rw [if_neg hm] at h1
    obtain ⟨w, hw, hne⟩ := movK_spec h1
    exact absurd (by rw [wv_eq (hW w hw) hv]; exact hfix w hw) hne

theorem ddiff_spec {p q x : ℕ} (hp : p < 31671) (hq : q < 31671) (hx : x < 31671)
    (h : ddiffK G p q x = true) :
    conjPt p * conjPt q * (d * d1) ≠ d * d1 * (conjPt p * conjPt q) := by
  intro e
  unfold ddiffK at h
  have h0 : (0 : ℕ) < 31671 := by norm_num
  have h1 : (1 : ℕ) < 31671 := by norm_num
  have e' := congrArg (fun g => idx 31671 g x) e
  simp only [idx_mul] at e'
  rw [tA_eq h1 hx, tA_eq h0 (idx_lt _ hx), tA_eq hq (idx_lt _ (idx_lt _ hx)),
    tA_eq hp (idx_lt _ (idx_lt _ (idx_lt _ hx))), tA_eq hq hx, tA_eq hp (idx_lt _ hx),
    tA_eq h1 (idx_lt _ (idx_lt _ hx)), tA_eq h0 (idx_lt _ (idx_lt _ (idx_lt _ hx))),
    conjPt_zero] at h
  change Bool.not (Nat.beq _ _) = true at h
  rw [show conjPt 1 = d1 from rfl, e'] at h
  simp at h

theorem witK_spec {p q : ℕ} : ∀ {X : List ℕ}, List.rec (motive := fun _ => Bool) false
    (fun x _ ih3 => bIf(ddiffK G p q x, true, ih3)) X = true → ∃ x ∈ X, ddiffK G p q x = true
  | [], h => absurd h (by simp)
  | x :: X, h => by
    change Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false
      (fun x _ ih3 => bIf(ddiffK G p q x, true, ih3)) X) true (ddiffK G p q x) = true at h
    rw [bRec_eq] at h
    by_cases hx : ddiffK G p q x = true
    · exact ⟨x, List.mem_cons_self, hx⟩
    · rw [if_neg hx] at h
      obtain ⟨y, hy, e⟩ := witK_spec h
      exact ⟨y, List.mem_cons_of_mem x hy, e⟩

theorem pick3 {a b c L : Bool} (ha : a = false) (hb : b = false) (hc : c = true)
    (h : bIf(a, true, bIf(b, true, bIf(c, L, true))) = true) : L = true := by
  subst ha
  subst hb
  subst hc
  exact h

theorem pairQ_spec {p : ℕ} {X : List ℕ} : ∀ {F : List ℕ}, List.rec (motive := fun _ => Bool) true
    (fun q _ ih2 => bAnd(bIf(Nat.beq p q, true,
      bIf(bAnd(Nat.ble p (nat_lit 1), Nat.ble q (nat_lit 1)), true,
        bIf(Nat.beq (tA G p q) q,
          List.rec (motive := fun _ => Bool) false
            (fun x _ ih3 => bIf(ddiffK G p q x, true, ih3)) X, true))), ih2)) F = true →
    ∀ q ∈ F, p ≠ q → ¬ (p ≤ 1 ∧ q ≤ 1) → tA G p q = q → ∃ x ∈ X, ddiffK G p q x = true
  | [], _, q, hq => absurd hq (by simp)
  | q0 :: F, h, q, hq => by
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    intro hpq h01 hfix
    rcases List.mem_cons.1 hq with e | hq
    · rw [e] at hpq h01 hfix ⊢
      generalize tA G p q0 = tq at h1 hfix
      have hb1 : Nat.beq p q0 = false := Bool.eq_false_iff.2 fun e => hpq (beq_of e)
      have hb2 : bAnd(Nat.ble p (nat_lit 1), Nat.ble q0 (nat_lit 1)) = false :=
        Bool.eq_false_iff.2 fun e => by
          obtain ⟨e1, e2⟩ := (CFSG.KS.bAnd_iff _ _).1 e
          exact h01 ⟨Nat.le_of_ble_eq_true e1, Nat.le_of_ble_eq_true e2⟩
      have hb3 : Nat.beq tq q0 = true := beq_true hfix
      exact witK_spec (pick3 hb1 hb2 hb3 h1)
    · exact pairQ_spec h2 q hq hpq h01 hfix

theorem pairP_spec {F X : List ℕ} : ∀ {P : List ℕ}, List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun q _ ih2 => bAnd(bIf(Nat.beq p q, true,
        bIf(bAnd(Nat.ble p (nat_lit 1), Nat.ble q (nat_lit 1)), true,
          bIf(Nat.beq (tA G p q) q,
            List.rec (motive := fun _ => Bool) false
              (fun x _ ih3 => bIf(ddiffK G p q x, true, ih3)) X, true))), ih2)) F, ih)) P = true →
    ∀ p ∈ P, List.rec (motive := fun _ => Bool) true
      (fun q _ ih2 => bAnd(bIf(Nat.beq p q, true,
        bIf(bAnd(Nat.ble p (nat_lit 1), Nat.ble q (nat_lit 1)), true,
          bIf(Nat.beq (tA G p q) q,
            List.rec (motive := fun _ => Bool) false
              (fun x _ ih3 => bIf(ddiffK G p q x, true, ih3)) X, true))), ih2)) F = true
  | [], _, p, hp => absurd hp (by simp)
  | p0 :: P, h, p, hp => by
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h1
    · exact pairP_spec h2 p hp

theorem pairsK_spec {F X : List ℕ} (h : pairsK G F X = true) :
    ∀ p ∈ F, ∀ q ∈ F, p ≠ q → ¬ (p ≤ 1 ∧ q ≤ 1) → tA G p q = q →
      ∃ x ∈ X, ddiffK G p q x = true := by
  intro p hp
  exact pairQ_spec (pairP_spec h p hp)

theorem pair_of {F X : List ℕ} (hF : ∀ p ∈ F, p < 31671) (hX : ∀ x ∈ X, x < 31671)
    (h : pairsK G F X = true) :
    ∀ p ∈ F, ∀ q ∈ F, p ≠ q → conjPt p * conjPt q = conjPt q * conjPt p →
      conjPt p * conjPt q * (d * d1) = d * d1 * (conjPt p * conjPt q) →
      (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0) := by
  intro p hp q hq hpq hc hpd
  by_cases h01 : p ≤ 1 ∧ q ≤ 1
  · omega
  · have hfix : tA G p q = q := by
      rw [tA_eq (hF p hp) (hF q hq)]
      have e := mem_centralizer_conjPt_iff (conjPt p) (hF q hq)
      rw [Subgroup.mem_centralizer_singleton_iff] at e
      exact e.1 hc
    obtain ⟨x, hx, hd⟩ := pairsK_spec h p hp q hq hpq h01 hfix
    exact absurd hpd (ddiff_spec (hF p hp) (hF q hq) (hX x hx) hd)

theorem hy_spec {h : List ℕ} {v0 : ℕ} {Y : List (List ℕ)} (hh : WOK h)
    (hY : ∀ t < 6, WOK (Y.getD t [])) (hv : v0 < 31671) (hc : hyK G h v0 Y = true) :
    idx 31671 (wE h) v0 = 0 ∧ ∀ t < 6, idx 31671 (wE h * wE (Y.getD t [])) v0 = t := by
  unfold hyK at hc
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
  refine ⟨by rw [← wv_eq hh hv]; exact beq_of h1, fun t ht => ?_⟩
  have e := beq_of (CFSG.KS.allN_spec h2 t ht)
  rw [wv_eq (hY t ht) hv, wv_eq hh (idx_lt _ hv)] at e
  rw [idx_mul]
  exact e

theorem comm_of_cw {u v : List ℕ} (hu : WOK u) (hv : WOK v)
    (h : ∀ t < 6, cwK G u v t = true) : wE u * wE v = wE v * wE u := by
  refine eq_of_base fun t ht => ?_
  have ht' : t < 31671 := by omega
  have e := beq_of (h t ht)
  rw [wv_eq hv ht', wv_eq hu (idx_lt _ ht'), wv_eq hu ht', wv_eq hv (idx_lt _ ht')] at e
  rw [idx_mul, idx_mul]
  exact e

theorem cb_spec {C B : List (List ℕ)} (hC : ∀ c ∈ C, WOK c) (hB : ∀ b ∈ B, WOK b)
    (h : cbK G C B = true) : ∀ c ∈ C, ∀ b ∈ B, wE c * wE b = wE b * wE c := by
  induction C with
  | nil => simp
  | cons c C ih =>
    change Bool.rec (motive := fun _ => Bool) false (cbK G C B)
      (List.rec (motive := fun _ => Bool) true
        (fun b _ ih2 => Bool.rec (motive := fun _ => Bool) false ih2 (allN 6 (cwK G c b))) B) =
        true at h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    intro c' hc' b hb
    rcases List.mem_cons.1 hc' with rfl | hc'
    · clear ih h2 h
      induction B with
      | nil => simp at hb
      | cons b0 B ihB =>
        obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h1
        rcases List.mem_cons.1 hb with rfl | hb
        · exact comm_of_cw (hC _ List.mem_cons_self) (hB _ List.mem_cons_self)
            (CFSG.KS.allN_spec h3)
        · exact ihB (fun b hb => hB b (List.mem_cons_of_mem _ hb)) hb h4
    · exact ih (fun c hc => hC c (List.mem_cons_of_mem _ hc)) h2 c' hc' b hb

theorem t2K0_eq {t : ℕ} (ht : t < 31671) : t2K0 G t = idx 31671 t2 t := by
  unfold t2K0
  rw [tA_eq (by norm_num) ht, tA_eq (by norm_num) (idx_lt _ ht),
    tA_eq (by norm_num) (idx_lt _ (idx_lt _ ht))]
  change _ = idx 31671 (d * conjPt 1 * conjPt 39) t
  rw [idx_mul, idx_mul, conjPt_zero]

theorem t2_spec {Q : List (List ℕ)} (hQ : ∀ w ∈ Q, WOK w) (h : t2K G Q = true) :
    ∀ w ∈ Q, wE w * t2 = t2 * wE w := by
  induction Q with
  | nil => simp
  | cons w Q ih =>
    change Bool.rec (motive := fun _ => Bool) false (t2K G Q) (allN 6 fun t =>
      Nat.beq (wv G w (t2K0 G t)) (t2K0 G (wv G w t))) = true at h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    intro w' hw'
    rcases List.mem_cons.1 hw' with rfl | hw'
    · refine eq_of_base fun t ht => ?_
      have ht' : t < 31671 := by omega
      have e := beq_of (CFSG.KS.allN_spec h1 t ht)
      have hw := hQ _ List.mem_cons_self
      rw [t2K0_eq ht', wv_eq hw (idx_lt _ ht'), wv_eq hw ht', t2K0_eq (idx_lt _ ht')] at e
      rw [idx_mul, idx_mul]
      exact e
    · exact ih (fun w hw => hQ w (List.mem_cons_of_mem _ hw)) h2 w' hw'

theorem fixQ_spec {W : List (List ℕ)} (hW : ∀ w ∈ W, WOK w) (h : fixQK G W = true) :
    ∀ w ∈ W, wE w ∈ Subgroup.centralizer ({d} : Set CFSG.Sporadic.Fi23.J) ⊓ Subgroup.centralizer ({d1} : Set CFSG.Sporadic.Fi23.J) := by
  induction W with
  | nil => simp
  | cons w W ih =>
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (fixQK G W) (Nat.beq (wv G w 1) 1)) (Nat.beq (wv G w 0) 0) = true at h
    obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    intro w' hw'
    rcases List.mem_cons.1 hw' with rfl | hw'
    · have hw := hW _ List.mem_cons_self
      rw [Subgroup.mem_inf, ← conjPt_zero, show d1 = conjPt 1 from rfl,
        mem_centralizer_conjPt_iff _ (by norm_num), mem_centralizer_conjPt_iff _ (by norm_num),
        ← wv_eq hw (by norm_num), ← wv_eq hw (by norm_num)]
      exact ⟨beq_of h1, beq_of h2⟩
    · exact ih (fun w hw => hW w (List.mem_cons_of_mem _ hw)) h3 w' hw'

private theorem en_sB (y : ℕ) (k : ℕ → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

private theorem en_bAnd (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

private theorem en_bIf (c a b : Bool) : bIf(c, a, b) = (if c = true then a else b) := by
  cases c <;> rfl

private theorem en_or {x y k : ℕ} (hx : x < 2 ^ k) (hy : 2 ^ k ∣ y) : x ||| y = x + y := by
  obtain ⟨q, rfl⟩ := hy
  rw [Nat.lor_comm, Nat.mul_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx,
    Nat.add_comm]

private theorem mk6K_eq {a0 a1 a2 a3 a4 a5 : ℕ} (h0 : a0 < 32768) (h1 : a1 < 32768)
    (h2 : a2 < 32768) (h3 : a3 < 32768) (h4 : a4 < 32768) :
    mk6K a0 a1 a2 a3 a4 a5 = a0 + 32768 * a1 + 1073741824 * a2 + 35184372088832 * a3 +
      1152921504606846976 * a4 + 37778931862957161709568 * a5 := by
  change a0 ||| (a1 <<< 15 ||| (a2 <<< 30 ||| (a3 <<< 45 ||| (a4 <<< 60 ||| a5 <<< 75)))) = _
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  have e4 : a4 * 1152921504606846976 ||| a5 * 37778931862957161709568 =
      a4 * 1152921504606846976 + a5 * 37778931862957161709568 :=
    en_or (k := 75) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e4]
  have e3 : a3 * 35184372088832 ||| (a4 * 1152921504606846976 + a5 * 37778931862957161709568) =
      a3 * 35184372088832 + (a4 * 1152921504606846976 + a5 * 37778931862957161709568) :=
    en_or (k := 60) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e3]
  have e2 : a2 * 1073741824 ||| (a3 * 35184372088832 + (a4 * 1152921504606846976 +
      a5 * 37778931862957161709568)) = a2 * 1073741824 + (a3 * 35184372088832 +
      (a4 * 1152921504606846976 + a5 * 37778931862957161709568)) :=
    en_or (k := 45) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e2]
  have e1 : a1 * 32768 ||| (a2 * 1073741824 + (a3 * 35184372088832 + (a4 * 1152921504606846976 +
      a5 * 37778931862957161709568))) = a1 * 32768 + (a2 * 1073741824 + (a3 * 35184372088832 +
      (a4 * 1152921504606846976 + a5 * 37778931862957161709568))) :=
    en_or (k := 30) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e1]
  have e0 : a0 ||| (a1 * 32768 + (a2 * 1073741824 + (a3 * 35184372088832 +
      (a4 * 1152921504606846976 + a5 * 37778931862957161709568)))) = a0 + (a1 * 32768 +
      (a2 * 1073741824 + (a3 * 35184372088832 + (a4 * 1152921504606846976 +
      a5 * 37778931862957161709568)))) :=
    en_or (k := 15) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e0]
  ring

private theorem ptK_eq (c t : ℕ) : ptK c t = c / 2 ^ (15 * t) % 32768 := by
  unfold ptK lnK
  change (c >>> (15 * t)) &&& (2 ^ 15 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem ptK_mk6 {a0 a1 a2 a3 a4 a5 : ℕ} (h0 : a0 < 32768) (h1 : a1 < 32768)
    (h2 : a2 < 32768) (h3 : a3 < 32768) (h4 : a4 < 32768) (h5 : a5 < 32768) :
    ptK (mk6K a0 a1 a2 a3 a4 a5) 0 = a0 ∧ ptK (mk6K a0 a1 a2 a3 a4 a5) 1 = a1 ∧
      ptK (mk6K a0 a1 a2 a3 a4 a5) 2 = a2 ∧ ptK (mk6K a0 a1 a2 a3 a4 a5) 3 = a3 ∧
      ptK (mk6K a0 a1 a2 a3 a4 a5) 4 = a4 ∧ ptK (mk6K a0 a1 a2 a3 a4 a5) 5 = a5 := by
  simp only [ptK_eq, mk6K_eq h0 h1 h2 h3 h4, Nat.reduceMul, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private noncomputable abbrev cd6 (x : CFSG.Sporadic.Fi23.J) : ℕ :=
  mk6K (idx 31671 x 0) (idx 31671 x 1) (idx 31671 x 2) (idx 31671 x 3) (idx 31671 x 4)
    (idx 31671 x 5)

private theorem idx_lt32 (x : J) {t : ℕ} (ht : t < 6) : idx 31671 x t < 32768 :=
  lt_trans (idx_lt x (by omega)) (by norm_num)

private theorem ptK_cd6 (x : J) : ∀ t < 6, ptK (cd6 x) t = idx 31671 x t := by
  intro t ht
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := ptK_mk6 (idx_lt32 x (t := 0) (by norm_num))
    (idx_lt32 x (t := 1) (by norm_num)) (idx_lt32 x (t := 2) (by norm_num))
    (idx_lt32 x (t := 3) (by norm_num)) (idx_lt32 x (t := 4) (by norm_num))
    (idx_lt32 x (t := 5) (by norm_num))
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact l0
  · exact l1
  · exact l2
  · exact l3
  · exact l4
  · exact l5

private theorem cd6_inj {x y : J} (h : cd6 x = cd6 y) : x = y := by
  apply eq_of_base
  intro t ht
  rw [← ptK_cd6 x t ht, ← ptK_cd6 y t ht, h]

private theorem actK_cd6 {w : List ℕ} (hw : WOK w) (x : J) : actK G w (cd6 x) = cd6 (wE w * x) := by
  have hw' : ∀ t < 6, wv G w (ptK (cd6 x) t) = idx 31671 (wE w * x) t := fun t ht => by
    rw [ptK_cd6 x t ht, wv_eq hw (idx_lt x (by omega)), idx_mul]
  unfold actK
  simp only [sN_eq]
  rw [hw' 0 (by norm_num), hw' 1 (by norm_num), hw' 2 (by norm_num), hw' 3 (by norm_num),
    hw' 4 (by norm_num), hw' 5 (by norm_num)]

private theorem enumIK_spec {W : List (List ℕ)} {m n PAR IMG : ℕ} {LT : List ℕ} {i : ℕ}
    (h : enumIK G W m n PAR IMG LT i = true) :
    (i = 0 → cdK IMG 0 = mk6K 0 1 2 3 4 5) ∧
      (i ≠ 0 → ppK PAR i < i ∧ pjK PAR i < m ∧ ltK LT (pjK PAR i) (ppK PAR i) = i) ∧
      ∀ j < m, ltK LT j i < n ∧ cdK IMG (ltK LT j i) = actK G (W.getD j []) (cdK IMG i) := by
  unfold enumIK at h
  rw [en_bAnd, Bool.and_eq_true, en_bIf] at h
  obtain ⟨h1, h2⟩ := h
  rw [en_sB] at h2
  refine ⟨fun hi => ?_, fun hi => ?_, fun j hj => ?_⟩
  · subst hi
    rw [if_pos (Nat.beq_refl 0)] at h1
    exact Nat.eq_of_beq_eq_true h1
  · have hb : ¬ Nat.beq i 0 = true := fun e => hi (Nat.eq_of_beq_eq_true e)
    rw [if_neg hb] at h1
    simp only [en_sB, en_bAnd, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
    exact h1
  · have h3 := CFSG.KS.allN_spec h2 j hj
    simp only [en_sB, en_bAnd, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h3
    exact h3

private theorem ordK_spec {IMG ORD n : ℕ} (h : ordK IMG ORD n = true) :
    (∀ k < n, lnK 16 ORD k < n) ∧
      ∀ k, k + 1 < n → cdK IMG (lnK 16 ORD k) < cdK IMG (lnK 16 ORD (k + 1)) := by
  unfold ordK at h
  rw [en_bAnd, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := CFSG.KS.allN_spec h2
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · by_cases hk' : k = n - 1
    · subst hk'
      exact h1
    · have h4 := h3 k (by rw [Nat.pred_eq_sub_one]; omega)
      simp only [en_sB, en_bAnd, Bool.and_eq_true, Nat.blt_eq] at h4
      exact h4.1
  · have h4 := h3 k (by rw [Nat.pred_eq_sub_one]; omega)
    simp only [en_sB, en_bAnd, Bool.and_eq_true, Nat.blt_eq] at h4
    exact h4.2

private theorem cd_inj_of_ord {IMG ORD n : ℕ} (h : ordK IMG ORD n = true) :
    ∀ i < n, ∀ k < n, cdK IMG i = cdK IMG k → i = k := by
  obtain ⟨hlt, hstep⟩ := ordK_spec h
  set o := lnK 16 ORD with ho
  have hmono : ∀ a b, a < b → b < n → cdK IMG (o a) < cdK IMG (o b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
      · exact lt_trans (ih h' (by omega)) (hstep b hb)
      · exact hstep a hb
  have hinj : Set.InjOn o (Finset.range n : Set ℕ) := by
    intro a ha b hb e
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact absurd (congrArg (cdK IMG) e) (ne_of_lt (hmono a b h' hb))
    · exact absurd (congrArg (cdK IMG) e).symm (ne_of_lt (hmono b a h' ha))
  have hsub : (Finset.range n).image o ⊆ Finset.range n := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (hlt a (Finset.mem_range.1 ha))
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  have hsurj : ∀ i < n, ∃ a < n, o a = i := by
    intro i hi
    have hm : i ∈ (Finset.range n).image o := by
      rw [heq]
      exact Finset.mem_range.2 hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hm
    exact ⟨a, Finset.mem_range.1 ha, rfl⟩
  intro i hi k hk e
  obtain ⟨a, ha, rfl⟩ := hsurj i hi
  obtain ⟨b, hb, rfl⟩ := hsurj k hk
  by_contra hne
  have hab : a ≠ b := fun h' => hne (by rw [h'])
  rcases Nat.lt_or_gt_of_ne hab with h' | h'
  · exact absurd e (ne_of_lt (hmono a b h' hb))
  · exact absurd e.symm (ne_of_lt (hmono b a h' ha))

theorem enum_sound {W : List (List ℕ)} {m n PAR IMG ORD : ℕ} {LT : List ℕ} (hm : m ≤ 4)
    (hW : ∀ j < m, WOK (W.getD j [])) (hn : 0 < n)
    (he : ∀ i < n, enumIK G W m n PAR IMG LT i = true) (ho : ordK IMG ORD n = true) :
    TabData (fun j => wE (W.getD j [])) (parOf n (ppK PAR) (pjK PAR)) (ltOf m n (ltK LT)) n m ∧
      ∀ i < n, ∀ t < 6, idx 31671 (tabElt (fun j => wE (W.getD j []))
        (parOf n (ppK PAR) (pjK PAR)) i) t = ptK (cdK IMG i) t := by
  set g : ℕ → J := fun j => wE (W.getD j []) with hg
  set par := parOf n (ppK PAR) (pjK PAR) with hpar
  have hpar_i : ∀ i < n, par[i]! = (ppK PAR i, pjK PAR i) := fun i hi =>
    ofFnG (fun i => (ppK PAR i, pjK PAR i)) hi
  have hsp := fun i hi => enumIK_spec (he i hi)
  have hcode : ∀ i < n, cdK IMG i = cd6 (tabElt g par i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases h0 : i = 0
      · subst h0
        rw [tabElt_zero, (hsp 0 hi).1 rfl]
        simp only [cd6, idx_one]
      · obtain ⟨hp, hj, hl⟩ := (hsp i hi).2.1 h0
        have hEi : tabElt g par i = g (pjK PAR i) * tabElt g par (ppK PAR i) := by
          rw [tabElt_succ g par (by rw [hpar_i i hi]; exact hp), hpar_i i hi]
        obtain ⟨-, hc⟩ := (hsp (ppK PAR i) (by omega)).2.2 _ hj
        rw [hl] at hc
        rw [hc, ih _ hp (by omega), hEi, actK_cd6 (hW _ hj)]
  refine ⟨⟨fun i hi0 hi => ?_, fun j hj i hi => ?_, fun i hi k hk e => ?_⟩, fun i hi t ht => ?_⟩
  · obtain ⟨hp, hj, -⟩ := (hsp i hi).2.1 (by omega)
    rw [hpar_i i hi]
    exact ⟨hp, hj⟩
  · have hL : ((ltOf m n (ltK LT))[j]!)[i]! = ltK LT j i := by
      rw [ofFnG (fun j => Array.ofFn (n := n) fun i => ltK LT j i.val) hj,
        ofFnG (fun i => ltK LT j i) hi]
    rw [hL]
    obtain ⟨hk, hc⟩ := (hsp i hi).2.2 j hj
    refine ⟨hk, cd6_inj ?_⟩
    rw [← actK_cd6 (hW _ hj), ← hcode i hi, ← hc, hcode _ hk]
  · exact cd_inj_of_ord ho i hi k hk (by rw [hcode i hi, hcode k hk, e])
  · rw [hcode i hi, ptK_cd6 _ t ht]

end CertificateChecks.KernelFi23Nt

end
