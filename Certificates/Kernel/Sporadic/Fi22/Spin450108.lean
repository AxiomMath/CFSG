module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLatticeCheck
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Spin450108

open CFSG.KC.Enum CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
open CFSG.Monster.B.Co2.Native

@[expose] def xorColsK (k c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => xorColsK k c n ^^^ (if c.testBit n then actCodes.getD (10 * k + n) 0 % 2 ^ 10 else 0)

theorem xorCols_eq (k c : Nat) : ∀ n ≤ 10, xorCols (actCols k) c n = xorColsK k c n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [xorCols, xorColsK, xorCols_eq k c n (by omega)]
    congr 2
    rw [actCols, getElem!_pos _ n (by simp; omega), Array.getElem_ofFn]

theorem applyCols_eq (k : Nat) : applyCols (actCols k) = fun c => xorColsK k c 10 := by
  funext c
  exact xorCols_eq k c 10 le_rfl

@[expose] def reduceL (BL : List (Nat × Nat)) (v : Nat) : Nat :=
  BL.foldl (fun v p => if v.testBit p.2 then v ^^^ p.1 else v) v

theorem reduce_eq (B : List Nat) (v : Nat) :
    reduce B v = reduceL (B.map fun b => (b, lead b)) v := by
  rw [reduceL, List.foldl_map]
  rfl

theorem reduceL_cons (p : Nat × Nat) (BL : List (Nat × Nat)) (v : Nat) :
    reduceL (p :: BL) v = reduceL BL (if v.testBit p.2 then v ^^^ p.1 else v) := rfl

@[expose] def ledK (p : Nat × Nat) : Bool := p.1.testBit p.2 && decide (p.1 < 2 ^ (p.2 + 1))

@[expose] def goodL : List (Nat × Nat) → Bool
  | [] => true
  | p :: BL => ledK p && BL.all (fun q => decide (q.2 < p.2)) && goodL BL

theorem goodL_led : ∀ {BL : List (Nat × Nat)}, goodL BL = true → ∀ q ∈ BL, ledK q = true
  | [], _, q, hq => absurd hq List.not_mem_nil
  | p :: BL, h, q, hq => by
    simp only [goodL, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1.1
    · exact goodL_led h.2 q hq

theorem high_false {p : Nat × Nat} (h : ledK p = true) {j : Nat} (hj : p.2 < j) :
    p.1.testBit j = false := by
  simp only [ledK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Nat.testBit_lt_two_pow
    (lt_of_lt_of_le h.2 (Nat.pow_le_pow_right (by decide) (by omega)))

theorem keep_bit {k : Nat} : ∀ {BL : List (Nat × Nat)}, (∀ q ∈ BL, q.2 < k ∧ ledK q = true) →
    ∀ v, (reduceL BL v).testBit k = v.testBit k
  | [], _, v => rfl
  | q :: BL, h, v => by
    rw [reduceL_cons, keep_bit (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]
    split_ifs
    · obtain ⟨h1, h2⟩ := h q List.mem_cons_self
      rw [Nat.testBit_xor, high_false h2 h1, Bool.xor_false]
    · rfl

theorem clear_keys : ∀ {BL : List (Nat × Nat)}, goodL BL = true →
    ∀ v, ∀ q ∈ BL, (reduceL BL v).testBit q.2 = false
  | [], _, _, q, hq => absurd hq List.not_mem_nil
  | p :: BL, h, v, q, hq => by
    have hl := goodL_led h
    simp only [goodL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hp, hlt⟩, hBL⟩ := h
    rw [reduceL_cons]
    rcases List.mem_cons.1 hq with rfl | hq
    · rw [keep_bit (fun q' hq' => ⟨hlt q' hq', goodL_led hBL q' hq'⟩)]
      have hb : q.1.testBit q.2 = true := by
        simp only [ledK, Bool.and_eq_true] at hp
        exact hp.1
      split_ifs with hv
      · rw [Nat.testBit_xor, hv, hb]
        rfl
      · simpa using hv
    · exact clear_keys hBL _ q hq

theorem reduceL_lt : ∀ {BL : List (Nat × Nat)}, (∀ q ∈ BL, q.1 < 2 ^ 10) →
    ∀ {v}, v < 2 ^ 10 → reduceL BL v < 2 ^ 10
  | [], _, _, hv => hv
  | q :: BL, h, v, hv => by
    rw [reduceL_cons]
    refine reduceL_lt (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) ?_
    split_ifs
    · exact Nat.xor_lt_two_pow hv (h q List.mem_cons_self)
    · exact hv

theorem dot_xor (m a b : Nat) : ∀ n, dotN m (a ^^^ b) n = (dotN m a n != dotN m b n)
  | 0 => rfl
  | n + 1 => by
    simp only [dotN]
    rw [dot_xor m a b n, Nat.testBit_xor]
    cases dotN m a n <;> cases dotN m b n <;> cases m.testBit n <;> cases a.testBit n <;>
      cases b.testBit n <;> rfl

theorem dot_reduce {m : Nat} : ∀ {BL : List (Nat × Nat)}, (∀ q ∈ BL, dotM m q.1 = false) →
    ∀ v, dotM m (reduceL BL v) = dotM m v
  | [], _, v => rfl
  | q :: BL, h, v => by
    rw [reduceL_cons, dot_reduce (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]
    split_ifs
    · unfold dotM
      rw [dot_xor]
      have := h q List.mem_cons_self
      unfold dotM at this
      rw [this]
      cases dotN m v 10 <;> rfl
    · rfl

theorem zero_of_bits {r : Nat} (hr : r < 2 ^ 10) (h : ∀ j < 10, r.testBit j = false) : r = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hj : j < 10
  · exact h j hj
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega)))

theorem dot_single {m r p : Nat} : ∀ n, p < n → (∀ j < n, j ≠ p → r.testBit j = false) →
    dotN m r n = (m.testBit p && r.testBit p)
  | 0, hp, _ => absurd hp (Nat.not_lt_zero _)
  | n + 1, hp, h => by
    simp only [dotN]
    by_cases hpn : p = n
    · subst hpn
      have h0 : ∀ j < p, r.testBit j = false := fun j hj => h j (by omega) (by omega)
      have hz : dotN m r p = false := by
        clear h hp
        induction p with
        | zero => rfl
        | succ q ih =>
          simp only [dotN]
          rw [ih (fun j hj => h0 j (by omega)), h0 q (by omega)]
          cases m.testBit q <;> rfl
      rw [hz]
      cases m.testBit p <;> cases r.testBit p <;> rfl
    · rw [dot_single n (by omega) (fun j hj hjp => h j (by omega) hjp), h n (by omega) (Ne.symm hpn)]
      cases m.testBit p <;> cases r.testBit p <;> cases m.testBit n <;> rfl

@[expose] noncomputable def forceP (l : List (Nat × Nat)) : (List (Nat × Nat) → Bool) → Bool :=
  List.rec (motive := fun _ => (List (Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun p _ ih k => strictB p.1 fun a => strictB p.2 fun b => ih fun ys => k ((a, b) :: ys)) l

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem forceP_eq : ∀ (l : List (Nat × Nat)) (k : List (Nat × Nat) → Bool), forceP l k = k l
  | [], _ => rfl
  | p :: ps, k => by
    change strictB p.1 (fun a => strictB p.2 fun b => forceP ps fun ys => k ((a, b) :: ys)) =
      k (p :: ps)
    rw [strictB_eq', strictB_eq', forceP_eq ps]

@[expose] def f1 (c : Nat) : Nat := xorColsK 1 c 10
@[expose] def f2 (c : Nat) : Nat := xorColsK 2 c 10

@[expose] def basisOK (x : Nat) (BL : List (Nat × Nat)) : Bool :=
  goodL BL && BL.all (fun q => decide (q.1 < 2 ^ 10)) &&
    bIf(dotM mMask x, BL.map Prod.snd == [9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
      BL.all (fun q => !dotM mMask q.1) &&
        (List.range 10).any fun p => mMask.testBit p && BL.map Prod.snd == ((List.range 10).reverse.erase p))

@[expose] noncomputable def xBody (x : Nat) : Bool :=
  x == 0 || x == eMask || forceP ((spinBasis f1 f2 x).map fun b => (b, lead b)) (basisOK x)

@[expose] noncomputable def chunk (s : Nat) : Bool := allN 32 fun d => xBody (32 * s + d)

theorem head : (decide (0 < eMask) && decide (eMask < 1024) && !dotM mMask eMask) = true := by
  decide +kernel

theorem xBody_all (hs : ∀ s < 32, chunk s = true) {x : Nat} (hx : x < 1024) : xBody x = true := by
  have h := CFSG.KS.allN_spec (hs (x / 32) (by omega)) (x % 32) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at h

theorem key_mem {BL : List (Nat × Nat)} {L : List Nat} (h : (BL.map Prod.snd == L) = true) {j : Nat}
    (hj : j ∈ L) : ∃ q ∈ BL, q.2 = j := by
  have e : BL.map Prod.snd = L := by simpa using h
  rw [← e] at hj
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
  exact ⟨q, hq, rfl⟩

theorem basis_sound {x : Nat} {BL : List (Nat × Nat)} (h : basisOK x BL = true) {y : Nat}
    (hy : y < 1024) : (reduceL BL y == 0 || (!dotM mMask x && dotM mMask y)) = true := by
  unfold basisOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hg, hlt⟩, hc⟩ := h
  have h1024 : (2 : Nat) ^ 10 = 1024 := rfl
  have hr : reduceL BL y < 2 ^ 10 := reduceL_lt hlt (by omega)
  have hk := clear_keys hg y
  cases hd : dotM mMask x
  · rw [hd] at hc
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨hdot, p, hp, hmp, hkeys⟩ := hc
    have hp10 : p < 10 := List.mem_range.1 hp
    have hbits : ∀ j < 10, j ≠ p → (reduceL BL y).testBit j = false := by
      intro j hj hjp
      obtain ⟨q, hq, rfl⟩ := key_mem hkeys
        (List.mem_erase_of_ne hjp |>.2 (List.mem_reverse.2 (List.mem_range.2 hj)))
      exact hk q hq
    cases hb : (reduceL BL y).testBit p
    · have : reduceL BL y = 0 := zero_of_bits hr fun j hj => by
        by_cases hjp : j = p
        · rw [hjp]
          exact hb
        · exact hbits j hj hjp
      rw [this]
      rfl
    · have h1 : dotM mMask (reduceL BL y) = true := by
        unfold dotM
        rw [dot_single 10 hp10 hbits, hmp, hb]
        rfl
      rw [dot_reduce hdot y] at h1
      rw [h1]
      simp
  · rw [hd] at hc
    have : reduceL BL y = 0 := zero_of_bits hr fun j hj => by
      obtain ⟨q, hq, rfl⟩ := key_mem hc (j := j) (by simp; omega)
      exact hk q hq
    rw [this]
    rfl

theorem body_of {x : Nat} (h : xBody x = true) :
    (x == 0 || x == eMask ||
      (allLt 1024 fun y => reduce (spinBasis f1 f2 x) y == 0 ||
        (!dotM mMask x && dotM mMask y))) = true := by
  unfold xBody at h
  rw [forceP_eq] at h
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro y hy
    rw [reduce_eq]
    simpa using basis_sound h hy

theorem spin (hs : ∀ s < 32, chunk s = true) :
    spinCheck (applyCols (actCols 1)) (applyCols (actCols 2)) eMask mMask = true := by
  rw [applyCols_eq, applyCols_eq]
  have e1 : (fun c => xorColsK 1 c 10) = f1 := rfl
  have e2 : (fun c => xorColsK 2 c 10) = f2 := rfl
  rw [e1, e2]
  unfold spinCheck
  have hh := head
  simp only [Bool.and_eq_true] at hh ⊢
  refine ⟨hh, ?_⟩
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro x hx
  exact body_of (xBody_all hs hx)

end CertificateChecks.KernelSpor.Spin450108

end
