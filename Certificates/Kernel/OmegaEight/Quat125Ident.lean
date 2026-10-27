module

public import Certificates.Kernel.OmegaEight.Quat125KD
import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Kernel.OmegaEight.E4O8CentGlue
public import Certificates.Kernel.OmegaEight.Roots127KB

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8

theorem q125sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem q125sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem q125bIfT {c t e : Bool} (hc : c = true) :
    Bool.rec (motive := fun _ => Bool) e t c = t := by
  subst hc; rfl

theorem q125bIfF {c t e : Bool} (hc : c = false) :
    Bool.rec (motive := fun _ => Bool) e t c = e := by
  subst hc; rfl

theorem q125nIfT {c : Bool} {t e : Nat} (hc : c = true) :
    Bool.rec (motive := fun _ => Nat) e t c = t := by
  subst hc; rfl

theorem q125nIfF {c : Bool} {t e : Nat} (hc : c = false) :
    Bool.rec (motive := fun _ => Nat) e t c = e := by
  subst hc; rfl

theorem q125beqT {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a

theorem q125beqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

theorem q125bAnd {a b : Bool} : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem q125blt {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem q125shift_or {a r : Nat} (hr : r < 2097152) :
    Nat.lor (Nat.shiftLeft a 21) r = a * 2097152 + r := by
  change a <<< 21 ||| r = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by norm_num; exact hr), Nat.shiftLeft_eq]

abbrev Q125E := Nat × Nat × Nat × Nat × List (Nat × Nat)

@[expose] def q125RecE (e : Q125E) : Nat := 1048576 + 128 * e.1 + 2 * e.2.1

@[expose] def q125Pk : List Nat → Nat
  | [] => 0
  | a :: l => q125Pk l * 2097152 + a

theorem q125Pk_inj : ∀ {l m : List Nat}, (∀ a ∈ l, 0 < a ∧ a < 2097152) →
    (∀ a ∈ m, 0 < a ∧ a < 2097152) → q125Pk l = q125Pk m → l = m
  | [], [], _, _, _ => rfl
  | [], b :: m, _, hm, h => by
    have := hm b (by simp)
    simp only [q125Pk] at h
    omega
  | a :: l, [], hl, _, h => by
    have := hl a (by simp)
    simp only [q125Pk] at h
    omega
  | a :: l, b :: m, hl, hm, h => by
    have ha := hl a (by simp)
    have hb := hm b (by simp)
    simp only [q125Pk] at h
    have e1 : a = b := by omega
    have e2 : q125Pk l = q125Pk m := by omega
    rw [e1, q125Pk_inj (fun x hx => hl x (by simp [hx])) (fun x hx => hm x (by simp [hx])) e2]

@[expose] def q125Nz (g : Nat → Nat) : List Nat → List Nat
  | [] => []
  | i :: l => if g i = 0 then q125Nz g l else g i :: q125Nz g l

theorem q125_mem_nz {g : Nat → Nat} {x : Nat} : ∀ {l : List Nat}, x ∈ q125Nz g l ↔
    ∃ i ∈ l, g i ≠ 0 ∧ g i = x
  | [] => by simp [q125Nz]
  | i :: l => by
    have ih := q125_mem_nz (g := g) (x := x) (l := l)
    by_cases h : g i = 0
    · simp only [q125Nz, if_pos h, ih, List.mem_cons]
      constructor
      · rintro ⟨j, hj, h1, h2⟩
        exact ⟨j, Or.inr hj, h1, h2⟩
      · rintro ⟨j, rfl | hj, h1, h2⟩
        · exact absurd h h1
        · exact ⟨j, hj, h1, h2⟩
    · simp only [q125Nz, if_neg h, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨j, hj, h1, h2⟩)
        · exact ⟨i, Or.inl rfl, h, rfl⟩
        · exact ⟨j, Or.inr hj, h1, h2⟩
      · rintro ⟨j, rfl | hj, h1, h2⟩
        · exact Or.inl h2.symm
        · exact Or.inr ⟨j, hj, h1, h2⟩

theorem q125_fold (g : Nat → Nat) : ∀ l : List Nat, (∀ i ∈ l, g i < 2097152) →
    l.foldr (fun i acc => strictN (g i) fun r =>
      nIf(Nat.beq r (nat_lit 0), acc, Nat.lor (Nat.shiftLeft acc (nat_lit 21)) r)) (nat_lit 0) =
      q125Pk (q125Nz g l)
  | [], _ => rfl
  | i :: l, h => by
    rw [List.foldr_cons, q125sN, q125_fold g l (fun j hj => h j (by simp [hj]))]
    by_cases h0 : g i = 0
    · rw [q125nIfT (q125beqT h0)]
      simp only [q125Nz, if_pos h0]
    · rw [q125nIfF (q125beqF h0), q125shift_or (h i (by simp))]
      simp only [q125Nz, if_neg h0, q125Pk]

theorem q125_recsJ : ∀ R : List Q125E, (∀ e ∈ R, e.1 < 8192 ∧ e.2.1 < 64) →
    recsJ R = q125Pk (R.map q125RecE)
  | [], _ => rfl
  | e :: R, h => by
    have he := h e (by simp)
    change strictN (recsJ R) (fun a => Nat.lor (q125RecE e) (Nat.shiftLeft a 21)) = _
    rw [q125sN, q125_recsJ R (fun x hx => h x (by simp [hx]))]
    have hr : q125RecE e < 2097152 := by unfold q125RecE; omega
    change q125RecE e ||| _ <<< 21 = _
    rw [Nat.lor_comm]
    exact q125shift_or hr

theorem q125_lk_le (s : Nat) : ∀ n L, Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih L => nIf(Nat.beq L (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (fld(L, nat_lit 6, nat_lit 18446744073709551615)) s,
        Nat.succ (Nat.land L (nat_lit 63)), strictN (Nat.shiftRight L (nat_lit 71)) ih))) n L ≤ 64
  | 0, _ => Nat.zero_le _
  | n + 1, L => by
    change Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
      (strictN (Nat.shiftRight L (nat_lit 71)) (Nat.rec (motive := fun _ => Nat → Nat)
        (fun _ => nat_lit 0) _ n)) (Nat.succ (Nat.land L (nat_lit 63)))
        (Nat.beq (fld(L, nat_lit 6, nat_lit 18446744073709551615)) s)) (nat_lit 0)
      (Nat.beq L (nat_lit 0)) ≤ 64
    cases Nat.beq L (nat_lit 0)
    · cases Nat.beq (fld(L, nat_lit 6, nat_lit 18446744073709551615)) s
      · change strictN _ _ ≤ 64
        rw [q125sN]
        exact q125_lk_le s n _
      · exact Nat.succ_le_succ Nat.and_le_right
    · exact Nat.zero_le _

theorem q125_lookL_le (L s : Nat) : lookL L s ≤ 64 := q125_lk_le s 38 L

theorem q125_rec0At (SC PT LT L i : Nat) : rec0At SC PT LT L i =
    if lookL L (matMulK (saAtK SC i) (saAtK SC i)) = 0 then 0 else
    if parK PT LT i = 0 then
      1048576 + 128 * i + 2 * (lookL L (matMulK (saAtK SC i) (saAtK SC i)) - 1) else 0 := by
  unfold rec0At
  rw [q125sN, q125sN]
  by_cases h1 : lookL L (matMulK (saAtK SC i) (saAtK SC i)) = 0
  · rw [q125nIfT (q125beqT h1), if_pos h1]
  · rw [q125nIfF (q125beqF h1), if_neg h1]
    by_cases h2 : parK PT LT i = 0
    · rw [q125nIfT (q125beqT h2), if_pos h2]
      rfl
    · rw [q125nIfF (q125beqF h2), if_neg h2]

@[expose] noncomputable def q125L1 : Nat := tyLK (ycK saCodes yIdxT) q125Ty 1

@[expose] noncomputable def q125R0 (i : Nat) : Nat := rec0At saCodes saParT saLabT q125L1 i

theorem q125_allRoots {f : Q125E → Bool} : ∀ {R : List Q125E}, allRoots R f = true →
    ∀ e ∈ R, f e = true
  | [], _, _, he => absurd he List.not_mem_nil
  | a :: R, h, e, he => by
    change bAnd(f a, allRoots R f) = true at h
    obtain ⟨h1, h2⟩ := q125bAnd.1 h
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    · exact q125_allRoots h2 e he

theorem q125_range : ∀ e ∈ roots, e.1 < 8192 ∧ e.2.1 < 64 := by
  intro e he
  have h := q125_allRoots kRange125 e he
  obtain ⟨i, k, r, c, pl⟩ := e
  obtain ⟨a1, a2⟩ := q125bAnd.1 h
  exact ⟨q125blt.1 a1, q125blt.1 a2⟩

theorem q125_R0_lt {i : Nat} (hi : i < 8192) : q125R0 i < 2097152 := by
  unfold q125R0
  rw [q125_rec0At]
  have := q125_lookL_le q125L1 (matMulK (saAtK saCodes i) (saAtK saCodes i))
  split_ifs <;> omega

theorem q125_roots_map : roots.map q125RecE = q125Nz q125R0 (List.range 8192) := by
  have h := kRoots125
  rw [q125sB, q125sB] at h
  have e := Nat.eq_of_beq_eq_true h
  unfold roots0K at e
  rw [CFSG.KC.Pack.foldN_eq] at e
  change (List.range 8192).foldr (fun i acc => strictN (q125R0 i) fun r =>
    nIf(Nat.beq r (nat_lit 0), acc, Nat.lor (Nat.shiftLeft acc (nat_lit 21)) r)) (nat_lit 0) = _ at e
  rw [q125_fold q125R0 _ (fun i hi => q125_R0_lt (List.mem_range.1 hi)),
    q125_recsJ roots q125_range] at e
  refine (q125Pk_inj ?_ ?_ e).symm
  · intro a ha
    obtain ⟨i, hi, h0, rfl⟩ := q125_mem_nz.1 ha
    exact ⟨Nat.pos_of_ne_zero h0, q125_R0_lt (List.mem_range.1 hi)⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    have := q125_range b hb
    unfold q125RecE
    omega

theorem q125_entry {e : Q125E} (he : e ∈ roots) : e.1 < 8192 ∧ parK saParT saLabT e.1 = 0 ∧
    lookL q125L1 (matMulK (saAtK saCodes e.1) (saAtK saCodes e.1)) = e.2.1 + 1 := by
  have hm : q125RecE e ∈ q125Nz q125R0 (List.range 8192) := by
    rw [← q125_roots_map]
    exact List.mem_map_of_mem he
  obtain ⟨i, hi, h0, hv⟩ := q125_mem_nz.1 hm
  obtain ⟨he1, he2⟩ := q125_range e he
  rw [List.mem_range] at hi
  unfold q125R0 at h0 hv
  rw [q125_rec0At] at h0 hv
  have hl := q125_lookL_le q125L1 (matMulK (saAtK saCodes i) (saAtK saCodes i))
  unfold q125RecE at hv
  split_ifs at h0 hv with h1 h2
  · exact absurd rfl h0
  · have ei : i = e.1 := by omega
    subst ei
    exact ⟨hi, h2, by omega⟩
  · exact absurd rfl h0

theorem q125_exists_entry {i k : Nat} (hi : i < 8192) (hp : parK saParT saLabT i = 0)
    (hl : lookL q125L1 (matMulK (saAtK saCodes i) (saAtK saCodes i)) = k + 1) :
    ∃ e ∈ roots, e.1 = i ∧ e.2.1 = k := by
  have hv : q125R0 i = 1048576 + 128 * i + 2 * k := by
    unfold q125R0
    rw [q125_rec0At, if_neg (by omega), if_pos hp, hl]
    rfl
  have hm : q125R0 i ∈ roots.map q125RecE := by
    rw [q125_roots_map]
    exact q125_mem_nz.2 ⟨i, List.mem_range.2 hi, by omega, rfl⟩
  obtain ⟨e, he, hev⟩ := List.mem_map.1 hm
  have hk := q125_lookL_le q125L1 (matMulK (saAtK saCodes i) (saAtK saCodes i))
  obtain ⟨he1, he2⟩ := q125_range e he
  rw [hv] at hev
  unfold q125RecE at hev
  exact ⟨e, he, by omega, by omega⟩

theorem q125_nz_nodup (g dec : Nat → Nat) : ∀ l : List Nat, l.Nodup →
    (∀ i ∈ l, g i ≠ 0 → dec (g i) = i) → ((q125Nz g l).map dec).Nodup
  | [], _, _ => List.nodup_nil
  | i :: l, hl, hd => by
    have hl' := (List.nodup_cons.1 hl)
    have ih := q125_nz_nodup g dec l hl'.2 (fun j hj => hd j (by simp [hj]))
    by_cases h0 : g i = 0
    · simp only [q125Nz, if_pos h0]
      exact ih
    · simp only [q125Nz, if_neg h0, List.map_cons]
      refine List.nodup_cons.2 ⟨fun hm => hl'.1 ?_, ih⟩
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
      obtain ⟨j, hj, hj0, rfl⟩ := q125_mem_nz.1 hx
      rw [hd j (by simp [hj]) hj0, hd i (by simp) h0] at hxe
      exact hxe ▸ hj

theorem q125_nodup : (roots.map Prod.fst).Nodup := by
  have e : roots.map Prod.fst = (roots.map q125RecE).map (fun x => x / 128 % 8192) := by
    rw [List.map_map]
    refine List.map_congr_left fun e he => ?_
    have := q125_range e he
    simp only [Function.comp_apply, q125RecE]
    omega
  rw [e, q125_roots_map]
  refine q125_nz_nodup _ _ _ List.nodup_range fun i hi h0 => ?_
  rw [List.mem_range] at hi
  unfold q125R0 at h0 ⊢
  rw [q125_rec0At] at h0 ⊢
  have hl := q125_lookL_le q125L1 (matMulK (saAtK saCodes i) (saAtK saCodes i))
  split_ifs at h0 ⊢ <;> first | exact absurd rfl h0 | omega

theorem q125_look {k : Nat} (hk : k < 38) (ht : q125Ty k = 1) :
    lookL q125L1 (saAtK (ycK saCodes yIdxT) k) = k + 1 := by
  have h := kLook125
  rw [q125sB, q125sB] at h
  have h' := CFSG.KC.Pack.allN_spec h k hk
  rw [q125bIfT (q125beqT ht)] at h'
  exact Nat.eq_of_beq_eq_true h'

theorem q125_and_two_pow (m p : Nat) : m &&& 2 ^ p = if m.testBit p then 2 ^ p else 0 := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : p = j
  · subst hj
    cases h : m.testBit p <;> simp [Nat.testBit_two_pow]
  · cases h : m.testBit p <;> simp [hj, Nat.testBit_two_pow]

theorem q125_bitK {m p : Nat} (h : bitK m p = true) : m.testBit p = true := by
  unfold bitK at h
  change Nat.blt 0 (m &&& 1 <<< p) = true at h
  rw [Nat.one_shiftLeft, q125_and_two_pow] at h
  cases e : m.testBit p
  · simp [e, Nat.blt_eq] at h
  · rfl

theorem q125_repsJ : ∀ {R : List Q125E} {x : Nat}, (repsJ R).testBit x = true →
    ∃ e ∈ R, e.2.2.1 = e.1 ∧ e.1 = x
  | [], x, h => by
    change (0 : Nat).testBit x = true at h
    simp at h
  | (i, k, r, c, pl) :: R, x, h => by
    change (strictN (repsJ R) fun a => nIf(Nat.beq r i, Nat.lor a (Nat.shiftLeft 1 i), a)).testBit x
      = true at h
    rw [q125sN] at h
    by_cases hri : r = i
    · rw [q125nIfT (q125beqT hri)] at h
      change (repsJ R ||| 1 <<< i).testBit x = true at h
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨e', he', h1⟩ := q125_repsJ h
        exact ⟨e', List.mem_cons_of_mem _ he', h1⟩
      · exact ⟨(i, k, r, c, pl), by simp, hri, of_decide_eq_true h⟩
    · rw [q125nIfF (q125beqF hri)] at h
      obtain ⟨e', he', h1⟩ := q125_repsJ h
      exact ⟨e', List.mem_cons_of_mem _ he', h1⟩

theorem q125_class {e : Q125E} (he : e ∈ roots) :
    (∃ e' ∈ roots, e'.1 = e.2.2.1 ∧ e'.2.2.1 = e'.1) ∧ e.2.2.2.1 < 8192 ∧
      parK saParT saLabT e.2.2.2.1 = 0 ∧
      matMulK (saAtK saCodes e.2.2.2.1) (saAtK saCodes e.1) =
        matMulK (saAtK saCodes e.2.2.1) (saAtK saCodes e.2.2.2.1) ∧
      matMulK (saAtK saCodes e.2.2.2.1) (saAtK (ycK saCodes yIdxT) e.2.1) =
        matMulK (saAtK (ycK saCodes yIdxT) e.2.1) (saAtK saCodes e.2.2.2.1) := by
  have h := kClass125
  rw [q125sB, q125sB] at h
  have h1 := q125_allRoots h e he
  obtain ⟨i, k, r, c, pl⟩ := e
  change bAnd(bitK (repsJ roots) r, bAnd(Nat.blt c 8192, bAnd(Nat.beq (parK saParT saLabT c) 0,
    strictB (saAtK saCodes c) fun C => strictB (saAtK (ycK saCodes yIdxT) k) fun y =>
      bAnd(Nat.beq (matMulK C (saAtK saCodes i)) (matMulK (saAtK saCodes r) C),
        Nat.beq (matMulK C y) (matMulK y C))))) = true at h1
  rw [q125sB, q125sB] at h1
  obtain ⟨a1, a2, a3, a4⟩ := (by simpa only [q125bAnd] using h1 :
    bitK (repsJ roots) r = true ∧ Nat.blt c 8192 = true ∧ Nat.beq (parK saParT saLabT c) 0 = true ∧
      (Nat.beq (matMulK (saAtK saCodes c) (saAtK saCodes i))
        (matMulK (saAtK saCodes r) (saAtK saCodes c)) = true ∧
      Nat.beq (matMulK (saAtK saCodes c) (saAtK (ycK saCodes yIdxT) k))
        (matMulK (saAtK (ycK saCodes yIdxT) k) (saAtK saCodes c)) = true))
  obtain ⟨e', he', h2, h3⟩ := q125_repsJ (q125_bitK a1)
  exact ⟨⟨e', he', h3, h2⟩, q125blt.1 a2, Nat.eq_of_beq_eq_true a3,
    Nat.eq_of_beq_eq_true a4.1, Nat.eq_of_beq_eq_true a4.2⟩

theorem q125_cntK (SC k R ry : Nat) : ∀ R0 : List Q125E, cntK SC R0 k R ry =
    R0.countP (fun e => bAnd(Nat.beq e.2.1 k, antiQK R ry (saAtK SC e.1)))
  | [] => rfl
  | (j, k', r, c, pl) :: R0 => by
    change strictN (cntK SC R0 k R ry) (fun a => nIf(bAnd(Nat.beq k' k, antiQK R ry (saAtK SC j)),
      Nat.succ a, a)) = _
    rw [q125sN, q125_cntK SC k R ry R0, List.countP_cons]
    cases bAnd(Nat.beq k' k, antiQK R ry (saAtK SC j)) <;> rfl

theorem q125_plK_cons (SC PT LT : Nat) (Ls : List (List Nat)) (C0 D0 C1 D1 C2 D2 k y R ry : Nat)
    (v tag : Nat) (pl : List (Nat × Nat)) (lo : Nat) :
    plK SC PT LT Ls C0 D0 C1 D1 C2 D2 k y R ry ((v, tag) :: pl) lo =
      strictN (saAtK SC v) fun V =>
      nIf(bAnd(Nat.blt lo v, bAnd(Nat.blt v (nat_lit 8192),
        bAnd(Nat.beq (parK PT LT v) (nat_lit 0),
        bAnd(Nat.beq (matMulK V V) y, bAnd(antiQK R ry V,
          tagOK SC Ls C0 D0 C1 D1 C2 D2 k y R V tag))))),
        strictN (plK SC PT LT Ls C0 D0 C1 D1 C2 D2 k y R ry pl v) fun n =>
          nIf(Nat.beq n (nat_lit 0), nat_lit 0, Nat.succ n), nat_lit 0) := rfl

theorem q125_plK {SC PT LT : Nat} {Ls : List (List Nat)} {C0 D0 C1 D1 C2 D2 k y R ry : Nat} :
    ∀ (pl : List (Nat × Nat)) (lo n : Nat),
    plK SC PT LT Ls C0 D0 C1 D1 C2 D2 k y R ry pl lo = n → n ≠ 0 →
    n = pl.length + 1 ∧ (pl.map Prod.fst).Nodup ∧ ∀ p ∈ pl, lo < p.1 ∧ p.1 < 8192 ∧
      parK PT LT p.1 = 0 ∧ matMulK (saAtK SC p.1) (saAtK SC p.1) = y ∧
      antiQK R ry (saAtK SC p.1) = true ∧
      tagOK SC Ls C0 D0 C1 D1 C2 D2 k y R (saAtK SC p.1) p.2 = true
  | [], lo, n, h, _ => by
    change 1 = n at h
    exact ⟨h.symm, List.nodup_nil, fun p hp => absurd hp List.not_mem_nil⟩
  | (v, tag) :: pl, lo, n, h, hn => by
    rw [q125_plK_cons, q125sN] at h
    beta_reduce at h
    cases hc : bAnd(Nat.blt lo v, bAnd(Nat.blt v (nat_lit 8192),
        bAnd(Nat.beq (parK PT LT v) (nat_lit 0),
        bAnd(Nat.beq (matMulK (saAtK SC v) (saAtK SC v)) y, bAnd(antiQK R ry (saAtK SC v),
          tagOK SC Ls C0 D0 C1 D1 C2 D2 k y R (saAtK SC v) tag)))))
    · rw [hc] at h
      exact absurd h.symm hn
    · rw [hc] at h
      change strictN (plK SC PT LT Ls C0 D0 C1 D1 C2 D2 k y R ry pl v)
        (fun n => nIf(Nat.beq n (nat_lit 0), nat_lit 0, Nat.succ n)) = n at h
      rw [q125sN] at h
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := (by simpa only [q125bAnd] using hc :
        Nat.blt lo v = true ∧ Nat.blt v 8192 = true ∧ Nat.beq (parK PT LT v) 0 = true ∧
        Nat.beq (matMulK (saAtK SC v) (saAtK SC v)) y = true ∧
        antiQK R ry (saAtK SC v) = true ∧
        tagOK SC Ls C0 D0 C1 D1 C2 D2 k y R (saAtK SC v) tag = true)
      set m := plK SC PT LT Ls C0 D0 C1 D1 C2 D2 k y R ry pl v with hm
      by_cases hm0 : m = 0
      · rw [q125nIfT (q125beqT hm0)] at h
        exact absurd h.symm hn
      · rw [q125nIfF (q125beqF hm0)] at h
        obtain ⟨e1, e2, e3⟩ := q125_plK pl v m rfl hm0
        refine ⟨by rw [← h, e1]; rfl, ?_, fun p hp => ?_⟩
        · rw [List.map_cons]
          refine List.nodup_cons.2 ⟨fun hv => ?_, e2⟩
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
          exact absurd (e3 p hp).1 (Nat.lt_irrefl _)
        · rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨q125blt.1 c1, q125blt.1 c2, Nat.eq_of_beq_eq_true c3,
              Nat.eq_of_beq_eq_true c4, c5, c6⟩
          · obtain ⟨d1, d2⟩ := e3 p hp
            exact ⟨(q125blt.1 c1).trans d1, d2⟩

theorem q125_partner {k R ry : Nat} {pl : List (Nat × Nat)} {Ls : List (List Nat)}
    {C0 D0 C1 D1 C2 D2 : Nat} (hk : k < 38) (ht : q125Ty k = 1)
    (hpl : plK saCodes saParT saLabT Ls C0 D0 C1 D1 C2 D2 k (saAtK (ycK saCodes yIdxT) k) R ry pl 0
      = Nat.succ (cntK saCodes roots k R ry))
    {v : Nat} (hv : v < 8192) (hp : parK saParT saLabT v = 0)
    (hsq : matMulK (saAtK saCodes v) (saAtK saCodes v) = saAtK (ycK saCodes yIdxT) k)
    (ha : antiQK R ry (saAtK saCodes v) = true) :
    ∃ tag, (v, tag) ∈ pl ∧
      tagOK saCodes Ls C0 D0 C1 D1 C2 D2 k (saAtK (ycK saCodes yIdxT) k) R (saAtK saCodes v) tag =
        true := by
  classical
  obtain ⟨e1, e2, e3⟩ := q125_plK pl 0 _ hpl (Nat.succ_ne_zero _)
  set P : Q125E → Bool := fun e => bAnd(Nat.beq e.2.1 k, antiQK R ry (saAtK saCodes e.1))
  have hcnt : cntK saCodes roots k R ry = (roots.filter P).length := by
    rw [q125_cntK, List.countP_eq_length_filter]
  have hS : ((roots.filter P).map Prod.fst).Nodup :=
    q125_nodup.sublist (List.filter_sublist.map _)
  have hmemS : ∀ w, w < 8192 → parK saParT saLabT w = 0 →
      matMulK (saAtK saCodes w) (saAtK saCodes w) = saAtK (ycK saCodes yIdxT) k →
      antiQK R ry (saAtK saCodes w) = true → w ∈ (roots.filter P).map Prod.fst := by
    intro w hw hpw hsw haw
    obtain ⟨e, he, rfl, hek⟩ := q125_exists_entry hw hpw (by rw [hsw, q125_look hk ht])
    refine List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, ?_⟩, rfl⟩
    exact q125bAnd.2 ⟨q125beqT hek, haw⟩
  have hsub : (pl.map Prod.fst).toFinset ⊆ ((roots.filter P).map Prod.fst).toFinset := by
    intro w hw
    rw [List.mem_toFinset] at hw ⊢
    obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hw
    obtain ⟨-, d1, d2, d3, d4, -⟩ := e3 p hp'
    exact hmemS _ d1 d2 d3 d4
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [List.toFinset_card_of_nodup hS, List.toFinset_card_of_nodup e2, List.length_map,
      List.length_map]
    have h1 : pl.length + 1 = cntK saCodes roots k R ry + 1 := e1.symm
    omega)
  have hvS := hmemS v hv hp hsq ha
  rw [← List.mem_toFinset, ← heq, List.mem_toFinset] at hvS
  obtain ⟨⟨v', tag⟩, hp', hv'⟩ := List.mem_map.1 hvS
  subst hv'
  exact ⟨tag, hp', (e3 _ hp').2.2.2.2.2⟩

theorem q125_pairs_at {e : Q125E} (he : e ∈ roots) (hr : e.2.2.1 = e.1) :
    plK saCodes saParT saLabT lists (r127M (wO (q125WW.getD 0 [])))
      (r127M (pinv (wO (q125WW.getD 0 [])))) (r127M (wO (q125WW.getD 1 [])))
      (r127M (pinv (wO (q125WW.getD 1 [])))) (saAtK saCodes wit37) (saAtK saCodes wit37i)
      e.2.1 (saAtK (ycK saCodes yIdxT) e.2.1) (saAtK saCodes e.1)
      (matMulK (saAtK saCodes e.1) (saAtK (ycK saCodes yIdxT) e.2.1)) e.2.2.2.2 0 =
    Nat.succ (cntK saCodes roots e.2.1 (saAtK saCodes e.1)
      (matMulK (saAtK saCodes e.1) (saAtK (ycK saCodes yIdxT) e.2.1))) := by
  have hlt := (q125_entry he).1
  obtain ⟨lo, hi, h, hlo, hhi⟩ : ∃ lo hi, q125Pairs lo hi = true ∧ lo ≤ e.1 ∧ e.1 < hi := by
    by_cases h0 : e.1 < 2048
    · exact ⟨0, 2048, kPairs125_0, Nat.zero_le _, h0⟩
    by_cases h1 : e.1 < 4096
    · exact ⟨2048, 4096, kPairs125_1, by omega, h1⟩
    by_cases h2 : e.1 < 6144
    · exact ⟨4096, 6144, kPairs125_2, by omega, h2⟩
    · exact ⟨6144, 8192, kPairs125_3, by omega, hlt⟩
  unfold q125Pairs at h
  simp only [q125sB] at h
  have h1 := q125_allRoots h e he
  obtain ⟨i, k, r, c, pl⟩ := e
  dsimp only at hr hlo hhi h1 ⊢
  simp only [pairsOK, rootB] at h1
  have hc : bAnd(Nat.beq r i, bAnd(Nat.ble lo i, Nat.blt i hi)) = true :=
    q125bAnd.2 ⟨q125beqT hr, q125bAnd.2 ⟨by rw [Nat.ble_eq]; exact hlo, q125blt.2 hhi⟩⟩
  rw [q125bIfT hc] at h1
  simp only [q125sB] at h1
  exact Nat.eq_of_beq_eq_true h1

section Acts


open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.KC.PCent

theorem q125_fldE (q o r : Nat) :
    Nat.land (Nat.shiftRight q o) (2 ^ r - 1) = q / 2 ^ o % 2 ^ r := by
  change (q >>> o) &&& (2 ^ r - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem q125_saAt (i : Nat) : saAtK saCodes i = saMat i := q125_fldE saCodes (64 * i) 64

theorem q125_YP_lt (k : Nat) : saAtK (ycK saCodes yIdxT) k < 2 ^ 64 := by
  change Nat.land _ 18446744073709551615 < 2 ^ 64
  exact Nat.and_lt_two_pow _ (by norm_num)

theorem q125_mm_lt (A B : Nat) : matMulK A B < 2 ^ 64 := by
  rw [matMulK_eq]
  exact matMulM_lt _ _

theorem q125_acts_mul {g h : Equiv.Perm (Fin 360)} {A B : Nat} (hg : Acts g A) (hh : Acts h B) :
    Acts (g * h) (matMulK A B) := by
  rw [matMulK_eq]
  exact acts_mul hg hh

theorem q125_acts_rep {k : Nat} (hk : k < 38) :
    Acts (repPerm k) (saAtK (ycK saCodes yIdxT) k) := by
  have h := kY127
  rw [q125sB] at h
  have hix : ix13 yIdxT k = yIdx k := q125_fldE yIdxT (13 * k) 13
  rw [Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec h k hk), hix, q125_saAt]
  exact acts_of_rep (repPerm_spec hk).1 (sa_facts.reps k hk).2

theorem q125_eqΩ {u v : Equiv.Perm (Fin 360)} (hu : u ∈ omegaT) (hv : v ∈ omegaT) {M : ℕ}
    (au : Acts u M) (av : Acts v M) : u = v := by
  have h : omegaRes ⟨u, hu⟩ = omegaRes ⟨v, hv⟩ := by
    refine Equiv.ext fun j => Fin.ext ?_
    rw [omegaRes_apply_val, omegaRes_apply_val]
    exact (au j j.2).2.trans (av j j.2).2.symm
  exact congrArg Subtype.val (omegaRes_injective h)

theorem q125_acts_pk {P M : Nat} (hP : CFSG.KC.BfsPin.PP 360 9 P)
    (h : actsK NSP NIP P M = true) : Acts (toPerm 360 9 P) M := by
  have hpm : pm P = true := CFSG.KC.Misc.ArrEnum.permB_of_pp hP
  rw [E4C.e4c_toPerm (CFSG.KC.Misc.ArrEnum.permB_of_pp hP)]
  exact acts_of_rep (rep_permOfArr (isInvA_of hpm)).1 (acts_of h)

theorem q125_rep_pc {p q : ℕ} {g h : Equiv.Perm (Fin 360)} (hp : cn p = true)
    (hq : cn q = true) (rp : Rep 360 (unpack 360 9 p) g) (rq : Rep 360 (unpack 360 9 q) h) :
    Rep 360 (unpack 360 9 (pc p q)) (g * h) := by
  rw [← compA_pc hp hq]
  exact rep_compA rp rq

theorem q125_rep_main {t : ℕ} (ht : t < 5) :
    Rep 360 (unpack 360 9 (mainK t)) (mainPerm t) := by
  rw [← (main_ok ht).1]
  exact (mainPerm_spec ht).1

theorem q125_main0 : mainPerm 0 = repPerm 10 := by
  rw [mainPerm, repPerm, mainArrs_getD (by norm_num), repArrs_getD (by norm_num)]
  rfl

theorem q125_memK {x : Nat} : ∀ {L : List Nat}, memK x L = true → x ∈ L
  | [], h => by
    change false = true at h
    exact absurd h (by decide)
  | a :: L, h => by
    change bIf(Nat.beq a x, true, memK x L) = true at h
    cases e : Nat.beq a x
    · rw [e] at h
      exact List.mem_cons_of_mem _ (q125_memK h)
    · rw [Nat.eq_of_beq_eq_true e]
      exact List.mem_cons_self

theorem q125_subK {L : List Nat} : ∀ {xs : List Nat}, subK xs L = true → ∀ x ∈ xs, x ∈ L
  | [], _, _, hx => absurd hx List.not_mem_nil
  | a :: xs, h, x, hx => by
    change bAnd(memK a L, subK xs L) = true at h
    obtain ⟨h1, h2⟩ := q125bAnd.1 h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact q125_memK h1
    · exact q125_subK h2 x hx

theorem q125_codesK (SC : Nat) : ∀ l : List Nat, codesK SC l = l.map (saAtK SC)
  | [] => rfl
  | a :: l => by
    change saAtK SC a :: codesK SC l = _
    rw [q125_codesK SC l, List.map_cons]

theorem q125_listAtK (SC : Nat) : ∀ (Ls : List (List Nat)) (j : Nat),
    listAtK SC Ls j = codesK SC (Ls.getD j [])
  | [], _ => rfl
  | l :: Ls, j => by
    change Bool.rec (motive := fun _ => List Nat) (listAtK SC Ls (Nat.sub j 1)) (codesK SC l)
      (Nat.beq j 0) = _
    cases e : Nat.beq j 0
    · have hj : j ≠ 0 := fun h => by rw [h] at e; exact absurd e (by decide)
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      change listAtK SC Ls (j' + 1 - 1) = _
      rw [Nat.add_sub_cancel, q125_listAtK SC Ls j']
      rfl
    · rw [Nat.eq_of_beq_eq_true e]
      rfl

end Acts

end CertificateChecks.KernelO8.Q125

end
