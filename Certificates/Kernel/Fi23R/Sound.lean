module

public import Certificates.Kernel.Fi23R.ChkDefs
public import Certificates.Kernel.Fi23M.Keys
public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.CFSGNative.Fi23.Centralizer
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23R

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23R CFSG.KS.Raw.Orb
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M

theorem tAf_zero (k m : Nat) : tAf G 0 k m = tb G 43 m := rfl

theorem tAf_succ (f k m : Nat) : tAf G (f + 1) k m = if k = 0 then tb G 43 m else
    if tb G 92 k = 1 then tb G 39 (tAf G f (tb G 91 k) (tb G 39 m))
    else tb G 40 (tAf G f (tb G 91 k) (tb G 41 m)) := by
  have e : tAf G (f + 1) k m = nIf(Nat.beq k (nat_lit 0), tb G (nat_lit 43) m,
      strictN (tb G (nat_lit 91) k) fun p => nIf(Nat.beq (tb G (nat_lit 92) k) (nat_lit 1),
        tb G (nat_lit 39) (tAf G f p (tb G (nat_lit 39) m)),
        tb G (nat_lit 40) (tAf G f p (tb G (nat_lit 41) m)))) := rfl
  rw [e, nIf_eq, strictN_eq, nIf_eq]
  simp only [Nat.beq_eq]

theorem tAf_lt : ∀ f k m, m < 31671 → tAf G f k m < 31671
  | 0, _, m, hm => rng 43 (by norm_num) m hm
  | f + 1, k, m, hm => by
    rw [tAf_succ]
    split_ifs
    · exact rng 43 (by norm_num) m hm
    · exact rng 39 (by norm_num) _ (tAf_lt f _ _ (rng 39 (by norm_num) m hm))
    · exact rng 40 (by norm_num) _ (tAf_lt f _ _ (rng 41 (by norm_num) m hm))

theorem tA_lt (k : Nat) {m : Nat} (hm : m < 31671) : tA G k m < 31671 := tAf_lt 200 k m hm

theorem tAf_treeAct {D bi : Table} (hD : ∀ m < 31671, ap D m = tb G 43 m)
    (hbi : ∀ m < 31671, ap bi m = tb G 41 m) :
    ∀ f k, k < 31671 → tb G 93 k < f → ∀ m < 31671,
      treeAct orbLit.par orbLit.lab orbLit.alpha orbLit.beta D bi k m = tAf G f k m
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, k, hk, hd, m, hm => by
    rw [treeAct.eq_def, tAf_succ]
    have ep : ap orbLit.par k = tb G 91 k := ap_tabOf 91 hk
    have el : ap orbLit.lab k = tb G 92 k := ap_tabOf 92 hk
    by_cases h0 : k = 0
    · subst h0
      rw [dif_neg (fun h => absurd h.1 (Nat.lt_irrefl 0)), if_pos rfl, hD m hm]
    · obtain ⟨hp, -, -⟩ := tr_pt hk h0
      have hpN : tb G 91 k < 31671 := by omega
      have hdp : tb G 93 (tb G 91 k) < f := by
        have := (dep_pt hk).2 h0
        omega
      rw [dif_pos ⟨Nat.pos_of_ne_zero h0, by rw [ep]; exact hp⟩, if_neg h0, ep, el]
      by_cases hl : tb G 92 k = 1
      · rw [if_pos (beq_iff_eq.2 hl), if_pos hl]
        have e1 : ap orbLit.alpha m = tb G 39 m := ap_tabOf 39 hm
        rw [e1, tAf_treeAct hD hbi f _ hpN hdp _ (rng 39 (by norm_num) m hm)]
        exact ap_tabOf 39 (tAf_lt f _ _ (rng 39 (by norm_num) m hm))
      · rw [if_neg (fun h => hl (beq_iff_eq.1 h)), if_neg hl]
        rw [hbi m hm, tAf_treeAct hD hbi f _ hpN hdp _ (rng 41 (by norm_num) m hm)]
        exact ap_tabOf 40 (tAf_lt f _ _ (rng 41 (by norm_num) m hm))

theorem lf_eq (c x : Nat) : lf G c x = if c < 128 then tb G c x else tA G (c - 128) x := by
  have e : lf G c x = nIf(Nat.blt c (nat_lit 128), tb G c x, tA G (Nat.sub c (nat_lit 128)) x) :=
    rfl
  rw [e, nIf_eq]
  simp only [Nat.blt_eq]
  rfl

theorem wa_nil (x : Nat) : wa G [] x = x := rfl

theorem wa_cons (c : Nat) (w : List Nat) (x : Nat) : wa G (c :: w) x = wa G w (lf G c x) := by
  have e : wa G (c :: w) x = strictN (lf G c x) (wa G w) := rfl
  rw [e, strictN_eq]

theorem wa_append : ∀ (u v : List Nat) (x : Nat), wa G (u ++ v) x = wa G v (wa G u x)
  | [], _, _ => rfl
  | c :: u, v, x => by rw [List.cons_append, wa_cons, wa_cons, wa_append u v]

theorem foldr_count (q : Nat → Bool) (lo : Nat) : ∀ (L : List Nat) (s : Nat),
    L.foldr (fun l s => nIf(q (Nat.add lo l), Nat.succ s, s)) s =
      s + (L.map (lo + ·)).countP q
  | [], s => rfl
  | a :: L, s => by
    rw [List.foldr_cons, foldr_count q lo L s, nIf_eq, List.map_cons, List.countP_cons]
    change (if q (lo + a) = true then _ else _) = _
    split_ifs with h <;> simp [h] <;> omega

theorem cntS_eq (q : Nat → Bool) (lo len : Nat) :
    cntS q lo len = ((List.range len).map (lo + ·)).countP q := by
  have e : cntS q lo len = foldN len (fun l s => nIf(q (Nat.add lo l), Nat.succ s, s)) 0 := rfl
  rw [e, foldN_eq, foldr_count, Nat.zero_add]

theorem cntS_add (q : Nat → Bool) (lo a b : Nat) :
    cntS q lo a + cntS q (lo + a) b = cntS q lo (a + b) := by
  rw [cntS_eq, cntS_eq, cntS_eq, List.range_add, List.map_append, List.countP_append,
    List.map_map]
  congr 2
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  omega

theorem cntS_zero (q : Nat → Bool) (n : Nat) : cntS q 0 n = (List.range n).countP q := by
  rw [cntS_eq]
  congr 1
  simp

theorem eqB_spec {u v : List Nat} (h : eqB G u v = true) : ∀ b < 6, wa G u b = wa G v b := by
  intro b hb
  have := allN_iff.1 h b hb
  exact Nat.eq_of_beq_eq_true this

theorem fxW_iff (w : List Nat) (x : Nat) : fxW G w x = true ↔ wa G w x = x := by
  unfold fxW
  rw [Nat.beq_eq]

theorem wapp_ind (P : Nat → Prop) (gens : List Nat)
    (hstep : ∀ i x, P x → P (tA G (gens.getD i 0) x)) : ∀ f c p, P p → P (wapp G gens f c p)
  | 0, _, _, h => h
  | f + 1, c, p, h => by
    have e : wapp G gens (f + 1) c p = nIf(Nat.beq c (nat_lit 0), p,
        wapp G gens f (Nat.shiftRight c (nat_lit 4))
          (tA G (List.getD gens (Nat.sub (Nat.land c (nat_lit 15)) (nat_lit 1)) (nat_lit 0)) p)) :=
      rfl
    rw [e, nIf_eq]
    split_ifs
    · exact h
    · exact wapp_ind P gens hstep f _ _ (hstep _ _ h)

theorem orbSl_spec {wY : List Nat} {ex : Nat → Bool} {Wr : Nat → Nat} {gens : List Nat}
    {r₁ r₂ lo len : Nat} (h : orbSl G wY ex Wr gens r₁ r₂ lo len = true) :
    ∀ l < len, ex (lo + l) = false → wa G wY (lo + l) = lo + l →
      ∃ c r, (r = r₁ ∨ r = r₂) ∧ wapp G gens 7 c r = lo + l := by
  intro l hl hex hfix
  have h1 := allN_iff.1 h l hl
  unfold orbAt at h1
  rw [bIf_eq, if_neg (by rw [show Nat.add lo l = lo + l from rfl, hex]; exact Bool.false_ne_true),
    bIf_eq, if_pos (by rw [show Nat.add lo l = lo + l from rfl, Nat.beq_eq]; exact hfix),
    strictB_eq, bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨-, h2⟩ := h1
  rw [nIf_eq] at h2
  refine ⟨_, _, ?_, Nat.eq_of_beq_eq_true h2⟩
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem exU_false {k : Nat} (h0 : k ≠ 0) (h1 : k ≠ 1) : exU k = false := by
  unfold exU
  rw [bIf_eq, if_neg (by rw [Nat.beq_eq]; exact h0)]
  cases e : Nat.beq k 1
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h1

theorem exT_false {k : Nat} (h0 : k ≠ 0) (h1 : k ≠ 1) (h39 : k ≠ 39) : exT k = false := by
  unfold exT
  rw [bIf_eq, exU_false h0 h1, if_neg Bool.false_ne_true]
  cases e : Nat.beq k 39
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h39

end CertificateChecks.KernelFi23R

end
