module

public import Certificates.Kernel.Sporadic.OrdCommon
public import Certificates.Data.Kernel.Spor.RelRange
public import CFSG.Certificates.Kernel.Spor.OrdSound

public section

namespace CFSG.KS.RelSeg

open CFSG.KC.Ord CFSG.KS.Ord

@[expose] def sel {α : Type} (lo hi : Nat) : Nat → List α → List α
  | _, [] => []
  | i, x :: l => if lo ≤ i ∧ i < hi then x :: sel lo hi (i + 1) l else sel lo hi (i + 1) l

theorem sel_nil_of_le {α : Type} {lo hi : Nat} : ∀ (i : Nat) (l : List α), hi ≤ i →
    sel lo hi i l = []
  | _, [], _ => rfl
  | i, x :: l, h => by
    rw [sel, ite_eq_right (by omega)]
    exact sel_nil_of_le (i + 1) l (by omega)

theorem sel_append {α : Type} {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    ∀ (i : Nat) (l : List α), sel lo mid i l ++ sel mid hi i l = sel lo hi i l
  | _, [] => rfl
  | i, x :: l => by
    have ih := sel_append h1 h2 (i + 1) l
    by_cases ha : lo ≤ i ∧ i < mid
    · rw [sel, ite_eq_left ha, sel, ite_eq_right (by omega), sel, ite_eq_left (by omega),
        List.cons_append, ih]
    · by_cases hb : mid ≤ i ∧ i < hi
      · have e0 : sel lo mid (i + 1) l = [] := sel_nil_of_le (i + 1) l (by omega)
        rw [e0, List.nil_append] at ih
        rw [sel, ite_eq_right ha, e0, List.nil_append, sel, ite_eq_left hb, sel,
          ite_eq_left (by omega), ih]
      · rw [sel, ite_eq_right ha, sel, ite_eq_right hb, sel, ite_eq_right (by omega), ih]

theorem sel_all {α : Type} {lo hi : Nat} : ∀ (i : Nat) (l : List α), lo ≤ i → i + l.length ≤ hi →
    sel lo hi i l = l
  | _, [], _, _ => rfl
  | i, x :: l, h1, h2 => by
    rw [List.length_cons] at h2
    rw [sel, ite_eq_left (by omega), sel_all (i + 1) l (by omega) (by omega)]

theorem sel_mem {α : Type} {lo hi : Nat} : ∀ {i : Nat} {l : List α} {x : α}, x ∈ sel lo hi i l → x ∈ l
  | _, [], _, h => by simp [sel] at h
  | i, y :: l, x, h => by
    rw [sel] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sel_mem h)
    · exact List.mem_cons_of_mem _ (sel_mem h)

theorem segProd_sel {R : Type} [Monoid R] {RB : Nat → Nat} {mul : Nat → Nat → Nat}
    {ONE Lg lo hi : Nat} {P : Nat → Prop} {M : Nat → R}
    (hmul : ∀ A B, P A → P B → P (mul A B) ∧ M (mul A B) = M A * M B) (hone : M ONE = 1) :
    ∀ (l : List (Nat × Bool)) (i acc : Nat), P acc → (∀ x ∈ l, P (letM RB Lg x)) →
      P (segProd RB mul ONE Lg lo hi l i acc) ∧
        M (segProd RB mul ONE Lg lo hi l i acc) =
          M acc * ((sel lo hi i l).map fun x => M (letM RB Lg x)).prod
  | [], _, _, hP, _ => ⟨hP, by rw [sel, List.map_nil, List.prod_nil, mul_one]; rfl⟩
  | x :: l, i, acc, hP, hl => by
    have e : segProd RB mul ONE Lg lo hi (x :: l) i acc =
        segProd RB mul ONE Lg lo hi l (Nat.succ i)
          (Bool.rec (motive := fun _ => Nat) acc
            ((fun m => Bool.rec (motive := fun _ => Nat) (mul acc m) m (Nat.beq acc ONE))
              (letM RB Lg x))
            (andB (Nat.ble lo i) (Nat.blt i hi))) :=
      strictN_eq _ (segProd RB mul ONE Lg lo hi l (Nat.succ i))
    have hx := hl x List.mem_cons_self
    have hl' : ∀ y ∈ l, P (letM RB Lg y) := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    rw [e]
    by_cases hin : lo ≤ i ∧ i < hi
    · have hb : andB (Nat.ble lo i) (Nat.blt i hi) = true := by
        rw [Nat.ble_eq.mpr hin.1, Nat.blt_eq.mpr hin.2]
        rfl
      obtain ⟨acc', hacc, hP', hM'⟩ : ∃ acc', (Bool.rec (motive := fun _ => Nat) acc
          ((fun m => Bool.rec (motive := fun _ => Nat) (mul acc m) m (Nat.beq acc ONE))
            (letM RB Lg x))
          (andB (Nat.ble lo i) (Nat.blt i hi))) = acc' ∧ P acc' ∧
            M acc' = M acc * M (letM RB Lg x) := by
        rw [hb]
        cases hq : Nat.beq acc ONE
        · exact ⟨mul acc (letM RB Lg x), rfl, hmul _ _ hP hx⟩
        · have hq' : acc = ONE := Nat.eq_of_beq_eq_true hq
          exact ⟨letM RB Lg x, rfl, hx, by rw [hq', hone, one_mul]⟩
      rw [hacc]
      obtain ⟨h1, h2⟩ := segProd_sel hmul hone l (i + 1) acc' hP' hl'
      refine ⟨h1, ?_⟩
      rw [h2, hM', sel, ite_eq_left hin, List.map_cons, List.prod_cons, mul_assoc]
    · have hb : andB (Nat.ble lo i) (Nat.blt i hi) = false := by
        cases h1 : Nat.ble lo i <;> cases h2 : Nat.blt i hi <;> try rfl
        exact absurd ⟨Nat.le_of_ble_eq_true h1, Nat.blt_eq.mp h2⟩ hin
      rw [hb]
      obtain ⟨h1, h2⟩ := segProd_sel hmul hone l (i + 1) acc hP hl'
      exact ⟨h1, by rw [h2, sel, ite_eq_right hin]⟩

variable (p d w S Lg : Nat) (RB : Nat → Nat) (rels : List (List (Nat × Bool)))

@[expose] def SegP (r lo hi Sin Sout : Nat) : Prop :=
  lo ≤ hi ∧ (Canon p d w Sin → Canon p d w Sout ∧ ordMat p d w S Sout =
    ordMat p d w S Sin * ((sel lo hi 0 (nthRel rels r)).map fun x => ordMat p d w S (letM RB Lg x)).prod)

variable {p d w S Lg RB rels}

theorem segP_join {r a b c S1 S2 S3 : Nat} (h1 : SegP p d w S Lg RB rels r a b S1 S2)
    (h2 : SegP p d w S Lg RB rels r b c S2 S3) : SegP p d w S Lg RB rels r a c S1 S3 := by
  refine ⟨h1.1.trans h2.1, fun hS => ?_⟩
  obtain ⟨hc2, e2⟩ := h1.2 hS
  obtain ⟨hc3, e3⟩ := h2.2 hc2
  refine ⟨hc3, ?_⟩
  rw [e3, e2, mul_assoc, ← List.prod_append, ← List.map_append, sel_append h1.1 h2.1]

private theorem nthRel_mem : ∀ (l : List (List (Nat × Bool))) (k : Nat), k < lenL l → nthRel l k ∈ l
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: l, k + 1, hk => by
    change nthRel l k ∈ _
    exact List.mem_cons_of_mem _ (nthRel_mem l k (Nat.lt_of_succ_lt_succ hk))

private theorem lenL_eq' {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenL l) = _
    rw [lenL_eq' l]
    rfl

private theorem rec_and' {f : Nat → Bool} : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m = true →
      ∀ g < m, f g = true
  | 0, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | m + 1, h, g, hg => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m)
        (f m) = true := h
    obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact rec_and' m h1 g hg
    · exact h2

theorem letM_canon {T L H CM RM ONE LV HV nb : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    (hroot : rootsOK RB (validM p nb L H) 1 (Lg + 1) = true)
    (hinv : invsOK RB (mulR p w S d T L H CM RM) (validM p nb L H) Lg ONE = true)
    {x : Nat × Bool} (hx : x.1 < Lg) : Canon p d w (letM RB Lg x) := by
  subst hnb
  obtain ⟨g, s⟩ := x
  cases s
  · have h := rec_and' (f := fun g => andB (validM p (d * S) L H (RB (Nat.add (Nat.succ Lg) g)))
      (Nat.beq (mulR p w S d T L H CM RM (RB (Nat.succ g)) (RB (Nat.add (Nat.succ Lg) g))) ONE))
      Lg hinv g hx
    exact validM_canon hc ((andB_iff _ _).1 h).1
  · have h := rec_and' (f := fun i => Bool.rec (motive := fun _ => Bool) true
      (validM p (d * S) L H (RB i)) (Nat.ble 1 i)) (Lg + 1) hroot (g + 1) (by simp at hx; omega)
    have hb1 : Nat.ble 1 (g + 1) = true := Nat.ble_eq.mpr (by omega)
    rw [hb1] at h
    exact validM_canon hc h

theorem segP_of_check {T L H CM RM ONE LV HV nb r lo hi Sin Sout : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    (hroot : rootsOK RB (validM p nb L H) 1 (Lg + 1) = true)
    (hinv : invsOK RB (mulR p w S d T L H CM RM) (validM p nb L H) Lg ONE = true)
    (hb : relsBounded rels Lg = true)
    (h : relSegOK RB (mulR p w S d T L H CM RM) rels ONE Lg r lo hi Sin Sout = true) :
    SegP p d w S Lg RB rels r lo hi Sin Sout := by
  have h' : andB (Nat.blt r (lenL rels)) (andB (Nat.blt lo hi) (andB (Nat.ble hi (lenL (nthRel rels r)))
      (Nat.beq (segProd RB (mulR p w S d T L H CM RM) ONE Lg lo hi (nthRel rels r) 0 Sin) Sout))) =
      true := h
  obtain ⟨hr, h'⟩ := (andB_iff _ _).1 h'
  obtain ⟨hlh, h'⟩ := (andB_iff _ _).1 h'
  obtain ⟨-, h'⟩ := (andB_iff _ _).1 h'
  have hseg := Nat.eq_of_beq_eq_true h'
  have hmem := nthRel_mem rels r (Nat.blt_eq.mp hr)
  have hbd := relsBounded_spec hb _ hmem
  refine ⟨Nat.le_of_lt (Nat.blt_eq.mp hlh), fun hS => ?_⟩
  have hs := segProd_sel (P := Canon p d w) (M := ordMat p d w S) (lo := lo) (hi := hi)
    (fun A B hA hB => mulR_sound hc hA hB) (one_sound hc).2 (nthRel rels r) 0 Sin hS
    (fun x hx => letM_canon hc hnb hroot hinv (hbd x hx))
  rw [hseg] at hs
  exact hs

theorem segP_of_relOK {T L H CM RM ONE LV HV nb r : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    (hroot : rootsOK RB (validM p nb L H) 1 (Lg + 1) = true)
    (hinv : invsOK RB (mulR p w S d T L H CM RM) (validM p nb L H) Lg ONE = true)
    (hb : relsBounded rels Lg = true)
    (h : relOK RB (mulR p w S d T L H CM RM) rels Lg ONE r = true) :
    SegP p d w S Lg RB rels r 0 (lenL (nthRel rels r)) ONE ONE :=
  segP_of_check hc hnb hroot hinv hb h

theorem rel_of_segP {T L H CM RM ONE LV HV r : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (h : SegP p d w S Lg RB rels r 0 (lenL (nthRel rels r)) ONE ONE) :
    ((nthRel rels r).map fun x => ordMat p d w S (letM RB Lg x)).prod = 1 := by
  obtain ⟨hONEc, hONE⟩ := one_sound hc
  obtain ⟨-, e⟩ := h.2 hONEc
  rw [hONE, one_mul, sel_all 0 _ (Nat.le_refl 0) (by rw [lenL_eq']; omega)] at e
  exact e.symm

theorem relOK_of_range {mul : Nat → Nat → Nat} {ONE lo n : Nat}
    (h : relsRangeOK RB mul rels Lg ONE lo n = true) :
    ∀ k < n, relOK RB mul rels Lg ONE (lo + k) = true :=
  rec_and' (f := fun k => relOK RB mul rels Lg ONE (Nat.add lo k)) n h

theorem rels_of_segP {T L H CM RM ONE LV HV : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (h : ∀ r < lenL rels, SegP p d w S Lg RB rels r 0 (lenL (nthRel rels r)) ONE ONE) :
    ∀ v ∈ rels, (v.map fun x => ordMat p d w S (letM RB Lg x)).prod = 1 := by
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hv
  have hr' : r < lenL rels := by rw [lenL_eq']; exact hr
  have e : nthRel rels r = rels[r] := by
    clear h hv hr'
    induction rels generalizing r with
    | nil => exact absurd hr (Nat.not_lt_zero _)
    | cons x l ih =>
      cases r with
      | zero => rfl
      | succ k =>
        change nthRel l k = _
        rw [ih k (by simp at hr; omega)]
        rfl
  rw [← e]
  exact rel_of_segP hc (h r hr')

end CFSG.KS.RelSeg

end
