module

public import Certificates.Kernel.TwoHSLe4.NormP
public import CFSG.Certificates.Kernel.F4M3BSound
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelTwoHSLe4.NormP

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.F4M3B CertificateChecks.KernelTwoHSLe4.Norm

variable {α β : Type}

theorem bindQ_eq (o : Ops α) (hbd : ∀ y k, o.bd y k = k y) (A : Q4 α) (k : Q4 α → α) :
    bindQ o A k = k A := by
  simp only [bindQ, hbd]

theorem bindL_eq (o : Ops α) (hbd : ∀ y k, o.bd y k = k y) :
    ∀ (L : List (Q4 α)) (k : List (Q4 α) → α), bindL o L k = k L
  | [], _ => rfl
  | A :: L, k => by
    change bindQ o A (fun A' => bindL o L fun L' => k (A' :: L')) = _
    rw [bindQ_eq o hbd]
    exact bindL_eq o hbd L _

theorem chkK_eq (o : Ops α) (hbd : ∀ y k, o.bd y k = k y) (b : R4) (L C : List R4)
    (h : ℕ → α) : chkK o b L C h = finK o b C (inQ o b h) (L.map fun s => mulM o (inQ o b h) (cQ o s))
      (L.map fun s => mulM o (cQ o s) (inQ o b h)) := by
  simp only [chkK, bindQ_eq o hbd, bindL_eq o hbd]

@[expose] def pm (f : α → β) (p : α × α) : β × β := (f p.1, f p.2)

@[expose] def Q4.map (f : α → β) (A : Q4 α) : Q4 β :=
  ⟨pm f A.e00, pm f A.e01, pm f A.e02, pm f A.e03, pm f A.e10, pm f A.e11, pm f A.e12, pm f A.e13,
    pm f A.e20, pm f A.e21, pm f A.e22, pm f A.e23, pm f A.e30, pm f A.e31, pm f A.e32,
    pm f A.e33⟩

@[expose] def V4.map (f : α → β) (v : V4 α) : V4 β := ⟨pm f v.v0, pm f v.v1, pm f v.v2, pm f v.v3⟩

section map

variable (o : Ops α) (o' : Ops β) (f : α → β) (ha : ∀ p q, f (o.a p q) = o'.a (f p) (f q))
  (hx : ∀ p q, f (o.x p q) = o'.x (f p) (f q)) (ht : f o.t = o'.t)
include ha hx

theorem dotE_map (a0 b0 a1 b1 a2 b2 a3 b3 : α × α) :
    pm f (dotE o a0 b0 a1 b1 a2 b2 a3 b3) =
      dotE o' (pm f a0) (pm f b0) (pm f a1) (pm f b1) (pm f a2) (pm f b2) (pm f a3) (pm f b3) := by
  simp only [dotE, addE, mulE, pm, ha, hx]

theorem mulM_map (A B : Q4 α) : (mulM o A B).map f = mulM o' (A.map f) (B.map f) := by
  simp only [mulM, Q4.map, dotE_map o o' f ha hx]

theorem mvM_map (A : Q4 α) (v : V4 α) : (mvM o A v).map f = mvM o' (A.map f) (v.map f) := by
  simp only [mvM, Q4.map, V4.map, dotE_map o o' f ha hx]

include ht

theorem zr_map : f (zr o) = zr o' := by simp only [zr, hx, ht]

theorem bnot_map' (p : α) : f (bnot o p) = bnot o' (f p) := by simp only [bnot, hx, ht]

theorem bor_map' (p q : α) : f (bor o p q) = bor o' (f p) (f q) := by simp only [bor, ha, hx]

theorem eqE_map (p q : α × α) : f (eqE o p q) = eqE o' (pm f p) (pm f q) := by
  simp only [eqE, pm, ha, hx, bnot_map' o o' f ha hx ht]

theorem eqM_map (A B : Q4 α) : f (eqM o A B) = eqM o' (A.map f) (B.map f) := by
  simp only [eqM, Q4.map, ha, eqE_map o o' f ha hx ht]

theorem eqV_map (v w : V4 α) : f (eqV o v w) = eqV o' (v.map f) (w.map f) := by
  simp only [eqV, V4.map, ha, eqE_map o o' f ha hx ht]

theorem cB_map (n : ℕ) : f (cB o n) = cB o' n := by
  unfold cB
  cases Nat.beq (Nat.mod n 2) 1
  · exact zr_map o o' f ha hx ht
  · exact ht

theorem cQ_map (c : R4) : (cQ o c).map f = cQ o' c := by
  simp only [cQ, Q4.map, cE, pm, cB_map o o' f ha hx ht]

theorem cV_map (v : RV) : (cV o v).map f = cV o' v := by
  simp only [cV, V4.map, cE, pm, cB_map o o' f ha hx ht]

theorem inQ_map (b : R4) (h : ℕ → α) : (inQ o b h).map f = inQ o' b (fun j => f (h j)) := by
  simp only [inQ, Q4.map, pm, cB_map o o' f ha hx ht]

theorem allA_map (L : List α) : f (allA o L) = allA o' (L.map f) := by
  induction L with
  | nil => exact ht
  | cons p L ih =>
    change f (o.a p (allA o L)) = o'.a (f p) (allA o' (L.map f))
    rw [ha, ih]

theorem anyA_map (L : List α) : f (anyA o L) = anyA o' (L.map f) := by
  induction L with
  | nil => exact zr_map o o' f ha hx ht
  | cons p L ih =>
    change f (bor o p (anyA o L)) = bor o' (f p) (anyA o' (L.map f))
    rw [bor_map' o o' f ha hx ht, ih]

theorem finK_map (b : R4) (C : List R4) (A : Q4 α) (P Q : List (Q4 α)) :
    f (finK o b C A P Q) = finK o' b C (A.map f) (P.map (Q4.map f)) (Q.map (Q4.map f)) := by
  have hc : ∀ c : R4, f (Bool.rec (zr o) (eqM o A (cQ o c)) (c.mod2 == b)) =
      Bool.rec (zr o') (eqM o' (A.map f) (cQ o' c)) (c.mod2 == b) := by
    intro c
    cases c.mod2 == b
    · exact zr_map o o' f ha hx ht
    · change f (eqM o A (cQ o c)) = eqM o' (A.map f) (cQ o' c)
      rw [eqM_map o o' f ha hx ht, cQ_map o o' f ha hx ht]
  simp only [finK, bor_map' o o' f ha hx ht, bnot_map' o o' f ha hx ht, ha,
    eqV_map o o' f ha hx ht, mvM_map o o' f ha hx, cV_map o o' f ha hx ht,
    allA_map o o' f ha hx ht, anyA_map o o' f ha hx ht, List.map_map, Function.comp_def,
    eqM_map o o' f ha hx ht, hc]

end map

@[expose] def enc (n : ℕ) : Bool × Bool := (Nat.beq (n % 2) 1, Nat.beq (n / 2 % 2) 1)

@[expose] def encQ (a : R4) : Q4 Bool :=
  ⟨enc a.a00, enc a.a01, enc a.a02, enc a.a03, enc a.a10, enc a.a11, enc a.a12, enc a.a13,
    enc a.a20, enc a.a21, enc a.a22, enc a.a23, enc a.a30, enc a.a31, enc a.a32, enc a.a33⟩

@[expose] def encV (v : RV) : V4 Bool := ⟨enc v.v0, enc v.v1, enc v.v2, enc v.v3⟩

theorem enc_mod (n : ℕ) : enc (n % 4) = enc n := by
  unfold enc
  have h1 : n % 4 % 2 = n % 2 := by omega
  have h2 : n % 4 / 2 % 2 = n / 2 % 2 := by omega
  rw [h1, h2]

theorem enc_add_lt : ∀ r < 4, ∀ s < 4, enc ((r + s) % 4) = addE boolOps (enc r) (enc s) := by
  decide

theorem enc_mul_lt : ∀ r < 4, ∀ s < 4, enc ((r * s) % 4) = mulE boolOps (enc r) (enc s) := by
  decide

theorem enc_add (n m : ℕ) : enc (n + m) = addE boolOps (enc n) (enc m) := by
  rw [← enc_mod (n + m), Nat.add_mod, enc_add_lt _ (Nat.mod_lt _ (by omega)) _
    (Nat.mod_lt _ (by omega)), enc_mod, enc_mod]

theorem enc_mul (n m : ℕ) : enc (n * m) = mulE boolOps (enc n) (enc m) := by
  rw [← enc_mod (n * m), Nat.mul_mod, enc_mul_lt _ (Nat.mod_lt _ (by omega)) _
    (Nat.mod_lt _ (by omega)), enc_mod, enc_mod]

theorem mulM_enc (a c : R4) : mulM boolOps (encQ a) (encQ c) = encQ (rmul a c) := by
  simp only [mulM, encQ, rmul, enc_mod, enc_add, enc_mul, dotE]

theorem mvM_enc (a : R4) (v : RV) : mvM boolOps (encQ a) (encV v) = encV (rmv a v) := by
  simp only [mvM, encQ, encV, rmv, enc_mod, enc_add, enc_mul, dotE]

theorem cB_bool (n : ℕ) : cB boolOps n = Nat.beq (n % 2) 1 := by
  unfold cB
  cases Nat.beq (Nat.mod n 2) 1 <;> rfl

theorem cQ_enc (c : R4) : cQ boolOps c = encQ c := by
  simp only [cQ, cE, encQ, enc, cB_bool]
  rfl

theorem cV_enc (v : RV) : cV boolOps v = encV v := by
  simp only [cV, cE, encV, enc, cB_bool]
  rfl

theorem eqE_lt : ∀ r < 4, ∀ s < 4, eqE boolOps (enc r) (enc s) = (r == s) := by decide

theorem eqM_enc {a c : R4} (ha : a.wf) (hc : c.wf) : eqM boolOps (encQ a) (encQ c) = (a == c) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := ha
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hc
  simp only [eqM, encQ, eqE_lt _ a0 _ c0, eqE_lt _ a1 _ c1, eqE_lt _ a2 _ c2, eqE_lt _ a3 _ c3,
    eqE_lt _ a4 _ c4, eqE_lt _ a5 _ c5, eqE_lt _ a6 _ c6, eqE_lt _ a7 _ c7, eqE_lt _ a8 _ c8,
    eqE_lt _ a9 _ c9, eqE_lt _ a10 _ c10, eqE_lt _ a11 _ c11, eqE_lt _ a12 _ c12,
    eqE_lt _ a13 _ c13, eqE_lt _ a14 _ c14, eqE_lt _ a15 _ c15, a_bool]
  rw [Bool.eq_iff_iff]
  cases a
  cases c
  simp only [Bool.and_eq_true, beq_iff_eq, R4.mk.injEq]

theorem eqV_enc {v w : RV} (hv : v.wf) (hw : w.wf) : eqV boolOps (encV v) (encV w) = (v == w) := by
  obtain ⟨v0, v1, v2, v3⟩ := hv
  obtain ⟨w0, w1, w2, w3⟩ := hw
  simp only [eqV, encV, eqE_lt _ v0 _ w0, eqE_lt _ v1 _ w1, eqE_lt _ v2 _ w2, eqE_lt _ v3 _ w3,
    a_bool]
  rw [Bool.eq_iff_iff]
  cases v
  cases w
  simp only [Bool.and_eq_true, beq_iff_eq, RV.mk.injEq]

theorem allA_bool (L : List Bool) : allA boolOps L = L.all id := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    change (p && allA boolOps L) = _
    rw [ih]
    rfl

theorem anyA_bool (L : List Bool) : anyA boolOps L = L.any id := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    change bor boolOps p (anyA boolOps L) = _
    rw [bor_bool, ih]
    rfl

theorem wf_tRV : tRV.wf := by
  unfold tRV toRV RV.wf
  dsimp only
  exact ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _⟩

theorem wf_zpRV : zpRV.wf := by
  unfold zpRV toRV RV.wf
  dsimp only
  exact ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _⟩

theorem finK_enc (b : R4) (L C : List R4) (hL : ∀ s ∈ L, s.wf) (hC : ∀ c ∈ C, c.wf) {a : R4}
    (ha : a.wf) :
    finK boolOps b C (encQ a) (L.map fun s => encQ (rmul a s)) (L.map fun s => encQ (rmul s a)) =
      (rmv a tRV == tRV || !((L.all fun s => L.any fun s' => rmul a s == rmul s' a) &&
        (L.all fun s' => L.any fun s => rmul a s == rmul s' a)) ||
        (rmv a tRV == zpRV && C.any fun c => (c.mod2 == b) && (a == c))) := by
  have hcand : (C.map fun c => Bool.rec (zr boolOps) (eqM boolOps (encQ a) (cQ boolOps c))
      (c.mod2 == b)) = C.map fun c => (c.mod2 == b) && (a == c) := by
    refine List.map_congr_left fun c hc => ?_
    rw [cQ_enc, eqM_enc ha (hC c hc)]
    cases c.mod2 == b <;> rfl
  have hP : ∀ s s' : R4,
      eqM boolOps (encQ (rmul a s)) (encQ (rmul s' a)) = (rmul a s == rmul s' a) :=
    fun _ _ => eqM_enc (wf_rmul _ _) (wf_rmul _ _)
  simp only [finK, cV_enc, mvM_enc, eqV_enc (wf_rmv _ _) wf_tRV, eqV_enc (wf_rmv _ _) wf_zpRV,
    hcand, allA_bool, anyA_bool, List.map_map, Function.comp_def, bor_bool, bnot_bool, a_bool,
    List.all_map, List.any_map, id, hP]

@[expose] def tbit (n m : ℕ) : Bool := m.testBit n

theorem ones_bit (k n : ℕ) (h : n < k) : tbit n (Nat.sub (Nat.pow 2 k) 1) = true := by
  rw [tbit, Nat.sub_eq, Nat.pow_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true h

theorem all_congr_mem {L : List R4} {p q : R4 → Bool} (h : ∀ a ∈ L, p a = q a) :
    L.all p = L.all q := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    rw [List.all_cons, List.all_cons, h y List.mem_cons_self,
      ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

theorem ent_lift (c y : ℕ) (hc : c < 2) :
    (cB boolOps c, decide (y % 2 = 1)) = enc (c + 2 * (y % 2)) := by
  rw [cB_bool]
  unfold enc
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> rw [h] <;> interval_cases c <;> rfl

theorem inQ_lift {b : R4} (hb : b.wf2) (n : ℕ) :
    inQ boolOps b (fun j => n.testBit j) = encQ (lift2 b (bitsOf n)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hb
  simp only [inQ, Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one, Nat.reducePow,
    encQ, lift2, bitsOf]
  rw [ent_lift _ _ h0, ent_lift _ _ h1, ent_lift _ _ h2, ent_lift _ _ h3, ent_lift _ _ h4,
    ent_lift _ _ h5, ent_lift _ _ h6, ent_lift _ _ h7, ent_lift _ _ h8, ent_lift _ _ h9,
    ent_lift _ _ h10, ent_lift _ _ h11, ent_lift _ _ h12, ent_lift _ _ h13, ent_lift _ _ h14,
    ent_lift _ _ h15]

theorem lift2_wf {b x : R4} (hb : b.wf2) (hx : x.wf2) : (lift2 b x).wf := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hb
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hx
  simp only [lift2, R4.wf]
  omega

theorem lift2_mod2 {b x : R4} (hb : b.wf2) : (lift2 b x).mod2 = b := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hb
  cases b
  simp only [lift2, R4.mod2, R4.mk.injEq] at *
  omega

theorem bitsOf_wf2 (n : ℕ) : (bitsOf n).wf2 := by
  simp only [bitsOf, R4.wf2]
  omega

theorem wf2B_wf2 {b : R4} (h : wf2B b = true) : b.wf2 := by
  simp only [wf2B, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem frcR_eq (b : R4) (k : R4 → Bool) : frcR b k = k b := by
  simp only [frcR, frc_eq]

theorem frcL_eq : ∀ (L : List R4) (k : List R4 → Bool), frcL L k = k L
  | [], _ => rfl
  | b :: L, k => by
    change frcR b (fun b' => frcL L fun L' => k (b' :: L')) = _
    rw [frcR_eq]
    exact frcL_eq L _

theorem fin_of_chkNG {b : R4} {L C : List R4} (h : chkNG b L C = true) {n : ℕ}
    (hn : n < 2 ^ 16) :
    finK boolOps b C (encQ (lift2 b (bitsOf n)))
      (L.map fun s => encQ (rmul (lift2 b (bitsOf n)) s))
      (L.map fun s => encQ (rmul s (lift2 b (bitsOf n)))) = true := by
  unfold chkNG at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hw, h⟩ := h
  have hb := wf2B_wf2 hw
  simp only [frcR_eq, frcL_eq, frc_eq] at h
  generalize hT : Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1 = T at h
  have hTn : tbit n T = true := by
    rw [← hT]
    exact ones_bit (Nat.pow 2 16) n hn
  have ha : ∀ p q, tbit n ((natOps T).a p q) = boolOps.a (tbit n p) (tbit n q) :=
    fun p q => Nat.testBit_and p q n
  have hx : ∀ p q, tbit n ((natOps T).x p q) = boolOps.x (tbit n p) (tbit n q) :=
    fun p q => Nat.testBit_xor p q n
  have e := congrArg (tbit n) (Nat.eq_of_beq_eq_true h)
  rw [hTn, chkK_eq _ (fun y k => frcN_eq y k),
    finK_map (natOps T) boolOps (tbit n) ha hx hTn] at e
  have hA : (inQ (natOps T) b fun j => pln j 16).map (tbit n) = encQ (lift2 b (bitsOf n)) := by
    rw [inQ_map (natOps T) boolOps (tbit n) ha hx hTn]
    simp only [tbit, pln_bit, hn, decide_true, Bool.true_and]
    exact inQ_lift hb n
  simp only [List.map_map, Function.comp_def, mulM_map (natOps T) boolOps (tbit n) ha hx,
    cQ_map (natOps T) boolOps (tbit n) ha hx hTn, hA, cQ_enc, mulM_enc] at e
  exact e

theorem any_filter_of (L : List R4) (p q : R4 → Bool) (h : ∀ x, q x = true → p x = true) :
    (L.filter p).any q = L.any q := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    by_cases hp : p y = true
    · simp [List.filter_cons, hp, ih]
    · have hq : q y = false := by
        cases hq : q y
        · rfl
        · exact absurd (h y hq) hp
      simp [List.filter_cons, hp, hq, ih]

theorem nCaseS_of_fin {a b : R4} (hab : a.mod2 = b)
    (h : (rmv a tRV == tRV || !((SL.all fun s => SL.any fun s' => rmul a s == rmul s' a) &&
        (SL.all fun s' => SL.any fun s => rmul a s == rmul s' a)) ||
        (rmv a tRV == zpRV && candR.any fun c => (c.mod2 == b) && (a == c))) = true) :
    nCaseS (compatS b) a = true := by
  have h1 : norm1B (compatS b) a = SL.all fun s => SL.any fun s' => rmul a s == rmul s' a := by
    unfold norm1B compatS
    rw [List.all_map]
    refine all_congr_mem fun s _ => ?_
    refine any_filter_of _ _ _ fun s' hs' => ?_
    rw [beq_iff_eq] at hs'
    rw [decide_eq_true_eq, ← hab, ← mod2_rmul, hs', mod2_rmul]
  have h2 : (candR.any fun c => (c.mod2 == b) && (a == c)) = decide (a ∈ candR) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨c, hc, hcc⟩
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcc
      rw [hcc.2]
      exact hc
    · intro ha
      refine ⟨a, ha, ?_⟩
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      exact ⟨hab, rfl⟩
  unfold nCaseS
  rw [h1, ← h2]
  exact h

theorem wf_SL : ∀ s ∈ SL, s.wf := by
  intro s hs
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hs
  simp only [S9.rl, R4.wf]
  omega

theorem wf_dR (P : ℕ) : (dR P).wf := by
  simp only [dR, fd, R4.wf]
  have h : ∀ x : ℕ, Nat.land x 3 < 4 := fun x => Nat.lt_of_le_of_lt (Nat.and_le_right) (by omega)
  exact ⟨h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _⟩

theorem wf_candK : ∀ c ∈ candK, c.wf := by
  intro c hc
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
  exact wf_dR _

theorem liftsOK_of_chkN (hcand : candK = candR) {b : R4} (h : chkN b = true) :
    liftsOK b = true := by
  have h' : chkNG b SL candK = true := h
  have hb : b.wf2 := by
    unfold chkNG at h'
    rw [Bool.and_eq_true] at h'
    exact wf2B_wf2 h'.1
  unfold liftsOK bitsN
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
  have hn' : n < 2 ^ 16 := List.mem_range.1 hn
  have ha := lift2_wf hb (bitsOf_wf2 n)
  have e := fin_of_chkNG h' hn'
  rw [finK_enc b SL candK wf_SL wf_candK ha, hcand] at e
  exact nCaseS_of_fin (lift2_mod2 hb) e

end CertificateChecks.KernelTwoHSLe4.NormP

end
