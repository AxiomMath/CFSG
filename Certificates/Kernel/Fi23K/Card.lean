module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public import Certificates.Kernel.Fi23K.Letters
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23K

open CFSG.KC.Fi23K CFSG.KS.PC CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native TauCeti

@[expose] def ActsAs (p : Equiv.Perm (Fin 31671)) (f : Nat → Nat) : Prop :=
  ∀ x (hx : x < 31671), (p ⟨x, hx⟩).val = f x

theorem ActsAs.ext {p q : Equiv.Perm (Fin 31671)} {f : Nat → Nat} (hp : ActsAs p f) (hq : ActsAs q f) :
    p = q := by
  ext ⟨x, hx⟩
  rw [hp x hx, hq x hx]

theorem ActsAs.mul {p q : Equiv.Perm (Fin 31671)} {f g : Nat → Nat} (hp : ActsAs p f) (hq : ActsAs q g) :
    ActsAs (p * q) (fun x => f (g x)) := by
  intro x hx
  rw [Equiv.Perm.mul_apply]
  have e : q ⟨x, hx⟩ = ⟨g x, by rw [← hq x hx]; exact (q ⟨x, hx⟩).isLt⟩ := Fin.ext (hq x hx)
  rw [e, hp]

theorem ActsAs.inv {p : Equiv.Perm (Fin 31671)} {f g : Nat → Nat} (hp : ActsAs p f)
    (hg : ∀ x < 31671, g x < 31671) (hfg : ∀ x < 31671, f (g x) = x) : ActsAs p⁻¹ g := by
  intro x hx
  have e : p⁻¹ ⟨x, hx⟩ = ⟨g x, hg x hx⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    apply Fin.ext
    rw [hp _ (hg x hx), hfg x hx]
  rw [e]

@[expose] noncomputable def permLI (f g : Nat → Nat) (hf : ∀ x < 31671, f x < 31671)
    (hg : ∀ x < 31671, g x < 31671) (hgf : ∀ x < 31671, g (f x) = x) : Equiv.Perm (Fin 31671) where
  toFun i := ⟨f i, hf i i.isLt⟩
  invFun i := ⟨g i, hg i i.isLt⟩
  left_inv i := Fin.ext (hgf i i.isLt)
  right_inv i := Fin.ext (right_inv_of_left hf hg hgf i i.isLt)

theorem permLI_acts {f g : Nat → Nat} (hf hg hgf) : ActsAs (permLI f g hf hg hgf) f :=
  fun _ _ => rfl

theorem x_inv {k : Nat} (hk : k < 10) {x : Nat} (hx : x < 31671) : tb G k (tb G k x) = x := by
  have h := eqv (k := k) (by omega) hx
  have e : EL k = [k, k] ∧ ER k = [] := by interval_cases k <;> decide +kernel
  rw [e.1, e.2] at h
  exact h

@[expose] noncomputable def xS (k : Nat) : Equiv.Perm (Fin 31671) :=
  if h : k < 10 then permLI (tb G k) (tb G k) (rng k (by omega)) (rng k (by omega))
    (fun _ hx => x_inv h hx) else 1

theorem xS_acts {k : Nat} (hk : k < 10) : ActsAs (xS k) (tb G k) := by
  unfold xS
  rw [dif_pos hk]
  exact permLI_acts _ _ _

noncomputable abbrev Xc : Subgroup (Equiv.Perm (Fin 31671)) := Subgroup.closure (xS '' {g | g < 10})

theorem word_acts : ∀ w : List Nat, (∀ r ∈ w, r < 10) →
    ActsAs (w.map xS).prod (wv G w) ∧ (w.map xS).prod ∈ Xc
  | [], _ => ⟨fun _ _ => rfl, Subgroup.one_mem _⟩
  | r :: w, hw => by
    obtain ⟨h1, h2⟩ := word_acts w fun s hs => hw s (List.mem_cons_of_mem r hs)
    have hr := hw r List.mem_cons_self
    rw [List.map_cons, List.prod_cons]
    exact ⟨(xS_acts hr).mul h1,
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨r, hr, rfl⟩) h2⟩

theorem pow_word (w : List Nat) : ∀ n x, wv G (List.flatten (List.replicate n w)) x =
    (wv G w)^[n] x
  | 0, x => rfl
  | n + 1, x => by
    rw [List.replicate_succ, List.flatten_cons, wv_append, Function.iterate_succ_apply',
      pow_word w n]

theorem rels_data :
    (∀ k < 10, EL k = [k, k] ∧ ER k = []) ∧
    (∀ p ∈ [((0 : Nat), (1 : Nat)), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 9), (3, 7), (7, 8)],
      p.1 < 10 ∧ p.2 < 10 ∧ ∃ k < 65, EL k = [p.1, p.2, p.1] ∧ ER k = [p.2, p.1, p.2]) ∧
    (∀ p ∈ [((0 : Nat), (2 : Nat)), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9),
      (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9),
      (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9),
      (3, 5), (3, 6), (3, 8), (3, 9),
      (4, 6), (4, 7), (4, 8), (4, 9),
      (5, 7), (5, 8), (5, 9), (6, 7), (6, 8), (7, 9), (8, 9)],
      p.1 < 10 ∧ p.2 < 10 ∧ ∃ k < 65, EL k = [p.1, p.2] ∧ ER k = [p.2, p.1]) ∧
    EL 55 = [44] ∧ ER 55 = [3, 2, 1, 3, 4, 5, 3, 7, 8] ∧ EL 56 = [45] ∧ ER 56 = [44, 44] ∧
    EL 57 = [46] ∧ ER 57 = [45, 45] ∧ EL 58 = [47] ∧ ER 58 = [46, 46] ∧ EL 59 = [47, 45] ∧
    ER 59 = [] ∧
    EL 60 = [48] ∧ ER 60 = [0, 1, 2, 3, 4, 5, 7] ∧ EL 61 = [49] ∧ ER 61 = [48, 48] ∧
    EL 62 = [50] ∧ ER 62 = [49, 49] ∧ EL 63 = [51] ∧ ER 63 = [50, 50] ∧ EL 64 = [51, 48] ∧
    ER 64 = [] := by
  decide +kernel

theorem eqAll {k : Nat} (hk : k < 150) {l r : List Nat} (hl : EL k = l) (hr : ER k = r) :
    ∀ x < 31671, wv G l x = wv G r x := by
  intro x hx
  rw [← hl, ← hr]
  exact eqv hk hx

theorem sq_pt {k : Nat} (hk : k < 10) {x : Nat} (hx : x < 31671) : tb G k (tb G k x) = x :=
  x_inv hk hx

theorem rel_value (v : List (Nat × Bool)) (hv : ∀ l ∈ v, l.2 = true ∧ l.1 < 10) :
    (v.map fun l => if l.2 then xS l.1 else (xS l.1)⁻¹).prod = ((v.map Prod.fst).map xS).prod := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.map_cons, List.prod_cons,
      if_pos (hv l List.mem_cons_self).1, ih fun l' h => hv l' (List.mem_cons_of_mem l h)]

theorem one_of_pt {w : List Nat} (hw : ∀ r ∈ w, r < 10) (h : ∀ x < 31671, wv G w x = x) :
    (w.map xS).prod = 1 :=
  ActsAs.ext (word_acts w hw).1 fun x hx => (h x hx).symm

theorem iter_congr {f g : Nat → Nat} (hf : ∀ y < 31671, f y < 31671) (hfg : ∀ y < 31671, f y = g y) :
    ∀ n x, x < 31671 → f^[n] x = g^[n] x
  | 0, _, _ => rfl
  | n + 1, x, hx => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hfg x hx]
    exact iter_congr hf hfg n _ (by rw [← hfg x hx]; exact hf x hx)

theorem iter_lt {f : Nat → Nat} (hf : ∀ y < 31671, f y < 31671) : ∀ n x, x < 31671 → f^[n] x < 31671
  | 0, _, hx => hx
  | n + 1, x, hx => by
    rw [Function.iterate_succ_apply]
    exact iter_lt hf n _ (hf x hx)

theorem iter_pows {p q r s : Nat} (hp : p < 91) (hq : q < 91) (hr : r < 91)
    (h2 : ∀ y < 31671, tb G q y = tb G p (tb G p y))
    (h4 : ∀ y < 31671, tb G r y = tb G q (tb G q y))
    (h8 : ∀ y < 31671, tb G s y = tb G r (tb G r y)) {y : Nat} (hy : y < 31671) :
    (tb G p)^[2] y = tb G q y ∧ (tb G p)^[8] y = tb G s y := by
  have i2 : ∀ y < 31671, (tb G p)^[2] y = tb G q y := fun y hy => (h2 y hy).symm
  have i4 : ∀ y < 31671, (tb G p)^[4] y = tb G r y := by
    intro y hy
    have e : (tb G p)^[4] y = (tb G p)^[2] ((tb G p)^[2] y) := Function.iterate_add_apply _ 2 2 y
    rw [e, i2 y hy, i2 _ (rng q hq y hy), h4 y hy]
  refine ⟨i2 y hy, ?_⟩
  have e : (tb G p)^[8] y = (tb G p)^[4] ((tb G p)^[4] y) := Function.iterate_add_apply _ 4 4 y
  rw [e, i4 y hy, i4 _ (rng r hr y hy), h8 y hy]

theorem long_U : (List.map (fun l => if l.2 then xS l.1 else (xS l.1)⁻¹)
    (List.flatten (List.replicate 10 [(3, true), (2, true), (1, true), (3, true), (4, true),
      (5, true), (3, true), (7, true), (8, true)]))).prod = 1 := by
  obtain ⟨-, -, -, e55l, e55r, e56l, e56r, e57l, e57r, e58l, e58r, e59l, e59r, -⟩ := rels_data
  rw [rel_value _ (by simp [List.replicate])]
  apply one_of_pt (by simp [List.replicate])
  intro x hx
  have hU := eqAll (by norm_num) e55l e55r
  have h2 := eqAll (by norm_num) e56l e56r
  have h4 := eqAll (by norm_num) e57l e57r
  have h8 := eqAll (by norm_num) e58l e58r
  have hf := eqAll (by norm_num) e59l e59r x hx
  have hw : List.map Prod.fst (List.flatten (List.replicate 10 [(3, true), (2, true), (1, true),
      (3, true), (4, true), (5, true), (3, true), (7, true), (8, true)])) =
      List.flatten (List.replicate 10 [3, 2, 1, 3, 4, 5, 3, 7, 8]) := by decide
  rw [hw, pow_word, iter_congr (g := tb G 44) (wv_lt rng _ (by decide))
    (fun y hy => (hU y hy).symm) 10 x hx]
  simp only [wv_cons, wv_nil] at h2 h4 h8 hf
  have e : (tb G 44)^[10] x = (tb G 44)^[8] ((tb G 44)^[2] x) := Function.iterate_add_apply _ 8 2 x
  rw [e, (iter_pows (by norm_num) (by norm_num) (by norm_num) h2 h4 h8 hx).1,
    (iter_pows (by norm_num) (by norm_num) (by norm_num) h2 h4 h8 (rng 45 (by norm_num) x hx)).2]
  exact hf

theorem long_V : (List.map (fun l => if l.2 then xS l.1 else (xS l.1)⁻¹)
    (List.flatten (List.replicate 9 [(0, true), (1, true), (2, true), (3, true), (4, true),
      (5, true), (7, true)]))).prod = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, e60l, e60r, e61l, e61r, e62l, e62r, e63l, e63r,
    e64l, e64r⟩ := rels_data
  rw [rel_value _ (by simp [List.replicate])]
  apply one_of_pt (by simp [List.replicate])
  intro x hx
  have hV := eqAll (by norm_num) e60l e60r
  have h2 := eqAll (by norm_num) e61l e61r
  have h4 := eqAll (by norm_num) e62l e62r
  have h8 := eqAll (by norm_num) e63l e63r
  have hf := eqAll (by norm_num) e64l e64r x hx
  have hw : List.map Prod.fst (List.flatten (List.replicate 9 [(0, true), (1, true), (2, true),
      (3, true), (4, true), (5, true), (7, true)])) =
      List.flatten (List.replicate 9 [0, 1, 2, 3, 4, 5, 7]) := by decide
  rw [hw, pow_word, iter_congr (g := tb G 48) (wv_lt rng _ (by decide))
    (fun y hy => (hV y hy).symm) 9 x hx]
  simp only [wv_cons, wv_nil] at h2 h4 h8 hf
  have e : (tb G 48)^[9] x = (tb G 48)^[8] ((tb G 48)^[1] x) := Function.iterate_add_apply _ 8 1 x
  rw [e, Function.iterate_one,
    (iter_pows (by norm_num) (by norm_num) (by norm_num) h2 h4 h8 (rng 48 (by norm_num) x hx)).2]
  exact hf

theorem rels_one : ∀ v ∈ CFSG.Sporadic.Bridge.Fi23GPL.Native.rels (),
    (v.map fun l => if l.2 then xS l.1 else (xS l.1)⁻¹).prod = 1 := by
  obtain ⟨hsq, hed, hne, e55l, e55r, e56l, e56r, e57l, e57r, e58l, e58r, e59l, e59r,
    e60l, e60r, e61l, e61r, e62l, e62r, e63l, e63r, e64l, e64r⟩ := rels_data
  intro v hv
  unfold CFSG.Sporadic.Bridge.Fi23GPL.Native.rels at hv
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_range,
    CFSG.Sporadic.Bridge.Fi23GPL.Native.powWord] at hv
  rcases hv with (((⟨k, hk, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) | (rfl | rfl | h))
  · rw [rel_value _ (by simp [hk])]
    apply one_of_pt (by simp [hk])
    intro x hx
    simpa [wv_cons, wv_nil] using sq_pt hk hx
  · obtain ⟨ha, hb', k, hk, hl, hr⟩ := hed p (by simpa using hp)
    have hb := eqAll (by omega) hl hr
    obtain ⟨a, b⟩ := p
    have hab : a < 10 ∧ b < 10 := ⟨ha, hb'⟩
    rw [rel_value _ (by simp [List.replicate, hab])]
    apply one_of_pt (by simp [List.replicate, hab])
    intro x hx
    have ra : ∀ y < 31671, tb G a y < 31671 := rng _ (by omega)
    have rb : ∀ y < 31671, tb G b y < 31671 := rng _ (by omega)
    have h1 := hb (tb G b (tb G a (tb G b x))) (rb _ (ra _ (rb _ hx)))
    simp only [List.replicate, List.flatten_cons, List.flatten_nil, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_nil, wv_cons, wv_nil] at h1 ⊢
    rw [h1, sq_pt hab.2 (ra _ (rb _ hx)), sq_pt hab.1 (rb _ hx), sq_pt hab.2 hx]
  · obtain ⟨ha, hb', k, hk, hl, hr⟩ := hne p (by simpa using hp)
    have hc := eqAll (by omega) hl hr
    obtain ⟨a, b⟩ := p
    have hab : a < 10 ∧ b < 10 := ⟨ha, hb'⟩
    rw [rel_value _ (by simp [List.replicate, hab])]
    apply one_of_pt (by simp [List.replicate, hab])
    intro x hx
    have ra : ∀ y < 31671, tb G a y < 31671 := rng _ (by omega)
    have rb : ∀ y < 31671, tb G b y < 31671 := rng _ (by omega)
    have h1 := hc (tb G a (tb G b x)) (ra _ (rb _ hx))
    simp only [List.replicate, List.flatten_cons, List.flatten_nil, List.map_append, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_nil, wv_cons, wv_nil] at h1 ⊢
    rw [h1, sq_pt hab.1 (rb _ hx), sq_pt hab.2 hx]
  · exact long_U
  · exact long_V
  · simp at h

end CFSG.KD.Fi23K

end
