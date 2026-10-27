module

public import Certificates.Kernel.He31064.Base
public import Certificates.Kernel.He31064.Lv
public import Certificates.Kernel.He31064.N0
public import Certificates.Kernel.He31064.N1
public import Certificates.Kernel.He31064.N2
public import Certificates.Kernel.He31064.N3
public import Certificates.Kernel.He31064.H0
public import Certificates.Kernel.He31064.H1
public import Certificates.Kernel.He31064.H2
public import Certificates.Kernel.He31064.H3
public import Certificates.Kernel.He31064.P0
public import Certificates.Kernel.He31064.P1
public import Certificates.Kernel.He31064.I
public import Certificates.Kernel.He31064.G
public import Certificates.Kernel.HeOrb.Final
public import CFSG.Certificates.Kernel.DcTupSound
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe

public section

namespace CFSG.KD.He31064

open CFSG.KC.DcTup
open CFSG.QuasithinUnique.K1.SporadicPerm (act act_eq act_lt act_mul act_one he_base_property)
open CFSG.Quasithin.H13.LocDbl.Dc (wprod wprod_cons wAB edgeList wprod_edge_mem eq_of_base
  lab_closure)
open DoubleCoset

set_option maxRecDepth 100000

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    have e : allN (n + 1) f = Bool.rec (motive := fun _ => Bool) false (allN n f) (f n) := rfl
    rw [e]
    cases h : f n
    · refine ⟨fun h' => absurd h' Bool.false_ne_true, fun H => ?_⟩
      rw [H n (Nat.lt_succ_self n)] at h
      exact absurd h.symm Bool.false_ne_true
    · refine ih.trans ⟨fun H i hi => ?_, fun H i hi => H i (Nat.lt_succ_of_lt hi)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact H i hi
      · exact h

theorem allR_get {lo len : Nat} {f : Nat → Bool} (h : allR lo len f = true) {i : Nat}
    (h1 : lo ≤ i) (h2 : i < lo + len) : f i = true := by
  have := allN_iff.mp h (i - lo) (by omega)
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rwa [e] at this

theorem cover {f : Nat → Bool} {w k : Nat} (hs : ∀ t < k, allR (w * t) w f = true) {i : Nat}
    (hi : i < w * k) : f i = true := by
  have hw : 0 < w := Nat.pos_of_ne_zero fun h => by rw [h, Nat.zero_mul] at hi; omega
  have ht : i / w < k := Nat.div_lt_of_lt_mul hi
  have h1 := Nat.div_add_mod i w
  have h2 := Nat.mod_lt i hw
  refine allR_get (hs (i / w) ht) ?_ ?_
  · generalize w * (i / w) = c at h1 ⊢
    omega
  · generalize w * (i / w) = c at h1 ⊢
    omega

theorem allL_iff {α : Type} {f : α → Bool} {l : List α} :
    allL f l = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun _ x hx => absurd hx List.not_mem_nil, fun _ => rfl⟩
  | cons x l ih =>
    have e : allL f (x :: l) = Bool.rec (motive := fun _ => Bool) false (allL f l) (f x) := rfl
    rw [e]
    cases h : f x
    · refine ⟨fun h' => absurd h' Bool.false_ne_true, fun H => ?_⟩
      rw [H x List.mem_cons_self] at h
      exact absurd h.symm Bool.false_ne_true
    · refine ih.trans ⟨fun H y hy => ?_, fun H y hy => H y (List.mem_cons_of_mem _ hy)⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h
      · exact H y hy

theorem nthD_eq {α : Type} (d : α) (l : List α) (i : Nat) : nthD d l i = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem nth_eq (l : List Nat) (i : Nat) : nth l i = l.getD i 0 := nthD_eq 0 l i

theorem nthL_eq (l : List (List Nat)) (i : Nat) : nthL l i = l.getD i [] := nthD_eq [] l i

theorem lenK_eq {α : Type} (l : List α) : lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.succ (lenK l) = _
    rw [ih]
    rfl

theorem memN_iff {c : Nat} {l : List Nat} : memN c l = true ↔ c ∈ l := by
  induction l with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | cons x l ih =>
    have e : memN c (x :: l) =
        Bool.rec (motive := fun _ => Bool) (memN c l) true (Nat.beq x c) := rfl
    rw [e, List.mem_cons]
    cases h : Nat.beq x c
    · rw [ih]
      have hne : c ≠ x := fun hc => by
        rw [hc, Nat.beq_refl] at h
        exact absurd h.symm Bool.false_ne_true
      exact ⟨Or.inr, fun h' => h'.resolve_left hne⟩
    · exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h).symm, fun _ => rfl⟩

theorem memP_spec {i j : Nat} : ∀ {P : List (Nat × Nat)}, memP i j P = true →
    ∃ k < P.length, P.getD k (0, 0) = (i, j)
  | [], h => absurd h Bool.false_ne_true
  | x :: P, h => by
    have e : memP i j (x :: P) = ((Nat.beq x.1 i && Nat.beq x.2 j) || memP i j P) := rfl
    rw [e, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | h
    · refine ⟨0, by simp, ?_⟩
      change x = (i, j)
      exact Prod.ext (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)
    · obtain ⟨k, hk, hk'⟩ := memP_spec h
      exact ⟨k + 1, by simp only [List.length_cons]; omega, hk'⟩

theorem allNeK_nodup {l : List Nat} (h : allNeK l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
    have e : allNeK (x :: l) = (allL (fun y => !Nat.beq y x) l && allNeK l) := rfl
    rw [e, Bool.and_eq_true] at h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, ih h.2⟩
    have := allL_iff.mp h.1 x hx
    rw [Nat.beq_refl] at this
    exact absurd this Bool.false_ne_true

theorem getD_mem {α : Type} {l : List α} {i : Nat} (hi : i < l.length) (d : α) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem tabOK_code {cs w : List Nat} {n X : Nat} (h : tabOK cs w n X = true) :
    ∀ p < n, im X p = wordK cs w p := fun p hp => Nat.eq_of_beq_eq_true (allN_iff.mp h p hp)

theorem stepOK_code {n g Y X : Nat} (h : stepOK n g Y X = true) :
    ∀ p < n, im X p = im g (im Y p) := fun p hp => Nat.eq_of_beq_eq_true (allN_iff.mp h p hp)

theorem idOK_code {n X : Nat} (h : idOK n X = true) : ∀ p < n, im X p = p :=
  fun p hp => Nat.eq_of_beq_eq_true (allN_iff.mp h p hp)

theorem wordInvL_eq (cs w ps : List Nat) : wordInvL cs w ps = ps.map (wordInvK cs w) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg (wordInvK cs w p :: ·) ih

theorem lens_parts : lenK reps = 133 ∧ lenK ri = 133 ∧ lenK lv = 6 ∧ lenK lvw = 6 ∧
    lenK rg = 2 ∧ lenK rgi = 2 ∧ lenK rgw = 2 ∧ (∀ j ∈ ri, j < 251) ∧
    (∀ w ∈ reps, ∀ l ∈ w, l < 4) ∧ (∀ w ∈ rgw, ∀ l ∈ w, l < 4) ∧
    (∀ w ∈ lvw, ∀ l ∈ w, l < 2) := by
  have h := CI.lens
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, -⟩, h13⟩, -⟩,
    -⟩, h16⟩, h17⟩, h18⟩, -⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h7,
    Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h9, Nat.eq_of_beq_eq_true h10,
    Nat.eq_of_beq_eq_true h11, fun j hj => ?_, fun w hw l hl => ?_, fun w hw l hl => ?_,
    fun w hw l hl => ?_⟩
  · simpa using allL_iff.mp h13 j hj
  · simpa using allL_iff.mp (allL_iff.mp h16 w hw) l hl
  · simpa using allL_iff.mp (allL_iff.mp h17 w hw) l hl
  · simpa using allL_iff.mp (allL_iff.mp h18 w hw) l hl

theorem W_letters {j : Nat} (hj : j < 133) : ∀ l ∈ W j, l < 4 := by
  obtain ⟨h1, -, -, -, -, -, -, -, h9, -, -⟩ := lens_parts
  refine h9 _ ?_
  unfold W
  rw [nthL_eq]
  exact getD_mem (by rw [← lenK_eq, h1]; exact hj) _

theorem hB : ∀ b ∈ B, b < 8330 := by
  intro b hb
  simp only [B, List.mem_cons, List.not_mem_nil, or_false] at hb
  omega

section Codes

variable {Γ : Type} [Group Γ] {n : Nat} [MulAction Γ (Fin n)]

theorem word_act {cs : List Nat} {L : List Γ} {k : Nat}
    (hc : ∀ l < k, ∀ p < n, im (nth cs l) p = act n (L.getD l 1) p) :
    ∀ w : List Nat, (∀ l ∈ w, l < k) → ∀ p < n, wordK cs w p = act n (wprod L w) p := by
  intro w
  induction w with
  | nil =>
    intro _ p hp
    simp only [wprod, List.map_nil, List.prod_nil]
    exact (act_one hp).symm
  | cons l w ih =>
    intro hw p hp
    have e : wordK cs (l :: w) p = im (nth cs l) (wordK cs w p) := rfl
    rw [e, ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) p hp, wprod_cons,
      act_mul _ _ hp]
    exact hc l (hw l List.mem_cons_self) _ (act_lt _ hp)

theorem wordInv_act {cs : List Nat} {L : List Γ}
    (hc : ∀ l < 4, ∀ p < n, im (nth cs l) p = act n (L.getD l 1) p)
    (hinv : ∀ l < 4, invL l < 4 ∧ L.getD (invL l) 1 = (L.getD l 1)⁻¹) :
    ∀ w : List Nat, (∀ l ∈ w, l < 4) → ∀ p < n, wordInvK cs w p = act n (wprod L w)⁻¹ p := by
  intro w
  induction w with
  | nil =>
    intro _ p hp
    simp only [wprod, List.map_nil, List.prod_nil, inv_one]
    exact (act_one hp).symm
  | cons l w ih =>
    intro hw p hp
    have hl := hw l List.mem_cons_self
    have e : wordInvK cs (l :: w) p = wordInvK cs w (im (nth cs (invL l)) p) := rfl
    rw [e, hc _ (hinv l hl).1 p hp, (hinv l hl).2,
      ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) _ (act_lt _ hp), ← act_mul _ _ hp,
      wprod_cons, mul_inv_rev]

theorem code_inv {c ci : Nat} {g : Γ} (hc : ∀ p < n, im c p = act n g p)
    (h : invOK n c ci = true) : ∀ p < n, im ci p = act n g⁻¹ p := by
  intro q hq
  have hp := act_lt g⁻¹ hq
  have h1 := allN_iff.mp h _ hp
  simp only [Bool.and_eq_true] at h1
  have h2 := Nat.eq_of_beq_eq_true h1.2
  rw [hc _ hp, ← act_mul _ _ hq, mul_inv_cancel, act_one hq] at h2
  exact h2

theorem chain_code {c : Nat} {g : Γ} (hg : ∀ p < n, im c p = act n g p) :
    ∀ (r : List Nat) (y k : Nat), (∀ p < n, im y p = act n (g ^ k) p) →
      List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun x _ ih y => Bool.rec (motive := fun _ => Bool) false (ih x) (stepOK n c y x)) r y =
        true →
      ∀ i < r.length, ∀ p < n, im (r.getD i 0) p = act n (g ^ (k + i + 1)) p := by
  intro r
  induction r with
  | nil => intro _ _ _ _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | cons x r ih =>
    intro y k hy h i hi p hp
    have h' : Bool.rec (motive := fun _ => Bool) false
        (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
          (fun x _ ih y => Bool.rec (motive := fun _ => Bool) false (ih x) (stepOK n c y x)) r x)
        (stepOK n c y x) = true := h
    cases hs : stepOK n c y x
    · rw [hs] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hs] at h'
      have hx : ∀ p < n, im x p = act n (g ^ (k + 1)) p := by
        intro p hp
        rw [stepOK_code hs p hp, hy p hp, hg _ (act_lt _ hp), ← act_mul _ _ hp, ← pow_succ']
      cases i with
      | zero => exact hx p hp
      | succ i =>
        have := ih x (k + 1) hx h' i (by simp only [List.length_cons] at hi; omega) p hp
        have e2 : k + (i + 1) + 1 = k + 1 + i + 1 := by omega
        rw [e2]
        exact this

theorem powOK_code {L : List Nat} {g : Γ} (hg : ∀ p < n, im (nth L 1) p = act n g p)
    (h : powOK n L = true) : ∀ k < L.length, ∀ p < n, im (L.getD k 0) p = act n (g ^ k) p := by
  cases L with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons e r =>
    have h' : Bool.rec (motive := fun _ => Bool) false
        (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
          (fun x _ ih y => Bool.rec (motive := fun _ => Bool) false (ih x)
            (stepOK n (nth (e :: r) 1) y x)) r e) (idOK n e) = true := h
    cases hi : idOK n e
    · rw [hi] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hi] at h'
      have he : ∀ p < n, im e p = act n (g ^ 0) p := fun p hp => by
        rw [pow_zero, act_one hp]
        exact idOK_code hi p hp
      intro k hk p hp
      cases k with
      | zero => exact he p hp
      | succ k =>
        have := chain_code hg r e 0 he h' k (by simp only [List.length_cons] at hk; omega) p hp
        rw [Nat.zero_add] at this
        exact this

theorem forall₂_of_getD {α β : Type} {Rel : α → β → Prop} {d : α} :
    ∀ {l : List α} {f : Nat → β}, (∀ k < l.length, Rel (l.getD k d) (f k)) →
      List.Forall₂ Rel l ((List.range l.length).map f)
  | [], _, _ => by
    simp only [List.length_nil, List.range_zero, List.map_nil]
    exact List.Forall₂.nil
  | x :: l, f, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    exact List.Forall₂.cons (h 0 (by simp))
      (forall₂_of_getD fun k hk => h (k + 1) (by simp only [List.length_cons]; omega))

end Codes

section He


open CFSG.Sporadic.He (J a b)

theorem act_idx (g : J) {p : Nat} (hp : p < 8330) :
    act 8330 g p = CFSG.Sporadic.Th.idx 8330 g p :=
  (act_eq g ⟨p, hp⟩).trans (CFSG.Sporadic.Th.idx_of_lt g hp).symm

theorem al_act : ∀ p < 8330, CFSG.KS.PEnum.r32 CFSG.KD.HeOrb.AL p = act 8330 a p := by
  intro p hp
  rw [act_idx a hp]
  have h := CFSG.Sporadic.He.rep_alpha p hp
  unfold CFSG.Sporadic.He.orb at h
  rwa [CFSG.KD.HeOrb.orbitData_eq, CFSG.KD.HeOrb.alpha_ap hp] at h

theorem be_act : ∀ p < 8330, CFSG.KS.PEnum.r32 CFSG.KD.HeOrb.BE p = act 8330 b p := by
  intro p hp
  rw [act_idx b hp]
  have h := CFSG.Sporadic.He.rep_beta p hp
  unfold CFSG.Sporadic.He.orb at h
  rwa [CFSG.KD.HeOrb.orbitData_eq, CFSG.KD.HeOrb.beta_ap hp] at h

theorem ab_code : ∀ l < 4, ∀ p < 8330,
    im (nth ab l) p = act 8330 ([a, b, a⁻¹, b⁻¹].getD l 1) p := by
  have h0 : ∀ p < 8330, im (nth ab 0) p = act 8330 a p := fun p hp =>
    (Nat.eq_of_beq_eq_true (allN_iff.mp CG.abA p hp)).trans (al_act p hp)
  have h1 : ∀ p < 8330, im (nth ab 1) p = act 8330 b p := fun p hp =>
    (Nat.eq_of_beq_eq_true (allN_iff.mp CG.abB p hp)).trans (be_act p hp)
  intro l hl
  interval_cases l
  · exact h0
  · exact h1
  · exact code_inv h0 CB.ab0
  · exact code_inv h1 CB.ab1

theorem ab_inv : ∀ l < 4, invL l < 4 ∧
    [a, b, a⁻¹, b⁻¹].getD (invL l) 1 = ([a, b, a⁻¹, b⁻¹].getD l 1)⁻¹ := by
  intro l hl
  interval_cases l
  · exact ⟨by decide, rfl⟩
  · exact ⟨by decide, rfl⟩
  · exact ⟨by decide, (inv_inv a).symm⟩
  · exact ⟨by decide, (inv_inv b).symm⟩

theorem word_code {w : List Nat} (hw : ∀ l ∈ w, l < 4) :
    ∀ p < 8330, wordK ab w p = act 8330 (wAB a b w) p :=
  word_act ab_code w hw

theorem wordInv_code {w : List Nat} (hw : ∀ l ∈ w, l < 4) :
    ∀ p < 8330, wordInvK ab w p = act 8330 (wAB a b w)⁻¹ p :=
  wordInv_act ab_code ab_inv w hw

@[expose] noncomputable def rt (t : Nat) : J := wAB a b (nthL rgw t)

@[expose] noncomputable def rts : List J := [rt 0, rt 1]

@[expose] noncomputable def Rg : Subgroup J := Subgroup.closure {x | x ∈ rts}

@[expose] noncomputable def lg (l : Nat) : J := wprod rts (nthL lvw l)

@[expose] noncomputable def Gs : List (List J) :=
  (List.range lv.length).map fun l => (List.range (lv.getD l []).length).map fun k => lg l ^ k

@[expose] noncomputable def xs (j : Nat) : J := wAB a b (W j)

theorem rg_code : ∀ t < 2, ∀ p < 8330, im (nth rg t) p = act 8330 (rts.getD t 1) p := by
  obtain ⟨-, -, -, -, -, -, h7, -, -, h10, -⟩ := lens_parts
  intro t ht
  have hw : ∀ l ∈ nthL rgw t, l < 4 :=
    h10 _ (by rw [nthL_eq]; exact getD_mem (by rw [← lenK_eq, h7]; exact ht) _)
  interval_cases t
  · exact fun p hp => (tabOK_code CB.rg0 p hp).trans (word_code hw p hp)
  · exact fun p hp => (tabOK_code CB.rg1 p hp).trans (word_code hw p hp)

theorem rgi_code : ∀ t < 2, ∀ p < 8330, im (nth rgi t) p = act 8330 (rts.getD t 1)⁻¹ p := by
  intro t ht
  interval_cases t
  · exact code_inv (rg_code 0 (by norm_num)) CB.rgi0
  · exact code_inv (rg_code 1 (by norm_num)) CB.rgi1

theorem getD_rts_mem (t : Nat) : rts.getD t 1 ∈ Rg := by
  rw [List.getD_eq_getElem?_getD]
  cases h : rts[t]? with
  | none => exact Subgroup.one_mem _
  | some y => exact Subgroup.subset_closure (List.mem_of_getElem? h)

theorem lg_mem (l : Nat) : lg l ∈ Rg := by
  unfold lg wprod
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hg
  exact getD_rts_mem t

theorem lv_code : ∀ l < 6, ∀ k < (nthL lv l).length, ∀ p < 8330,
    im ((nthL lv l).getD k 0) p = act 8330 (lg l ^ k) p := by
  obtain ⟨-, -, h3, h4, -, -, -, -, -, -, h11⟩ := lens_parts
  intro l hl
  have hw : ∀ t ∈ nthL lvw l, t < 2 :=
    h11 _ (by rw [nthL_eq]; exact getD_mem (by rw [← lenK_eq, h4]; exact hl) _)
  have hmem : nthL lv l ∈ lv := by
    rw [nthL_eq]
    exact getD_mem (by rw [← lenK_eq, h3]; exact hl) _
  have hg : ∀ p < 8330, im (nth (nthL lv l) 1) p = act 8330 (lg l) p := by
    have hwk : ∀ p < 8330, wordK rg (nthL lvw l) p = act 8330 (lg l) p :=
      word_act rg_code _ hw
    interval_cases l
    · exact fun p hp => (tabOK_code CL.w0 p hp).trans (hwk p hp)
    · exact fun p hp => (tabOK_code CL.w1 p hp).trans (hwk p hp)
    · exact fun p hp => (tabOK_code CL.w2 p hp).trans (hwk p hp)
    · exact fun p hp => (tabOK_code CL.w3 p hp).trans (hwk p hp)
    · exact fun p hp => (tabOK_code CL.w4 p hp).trans (hwk p hp)
    · exact fun p hp => (tabOK_code CL.w5 p hp).trans (hwk p hp)
  exact powOK_code hg (allL_iff.mp CL.pow _ hmem)

theorem hLG : List.Forall₂ (List.Forall₂ (CodeOf 8330)) lv Gs := by
  obtain ⟨-, -, h3, -, -, -, -, -, -, -, -⟩ := lens_parts
  refine forall₂_of_getD (d := []) fun l hl => ?_
  refine forall₂_of_getD (d := 0) fun k hk => ?_
  have hl6 : l < 6 := by rwa [← lenK_eq, h3] at hl
  rw [← nthL_eq] at hk ⊢
  exact lv_code l hl6 k hk

theorem hbase : ∀ g : J, (∀ p ∈ B, act 8330 g p = p) → g = 1 :=
  fun g hg => he_base_property g fun p hp => hg p hp

theorem ord : ordT 6174 C Q2 RW lv (2 :: 0 :: B) = 6174 := Nat.eq_of_beq_eq_true CB.ord

theorem nodes_all : ∀ i < 251, nodeOK i = true := by
  intro i hi
  by_cases h : i < 224
  · refine cover (f := nodeOK) (i := i) (w := 32) (k := 7) (fun t ht => ?_) (by omega)
    interval_cases t
    · exact CN.n0
    · exact CN.n1
    · exact CN.n2
    · exact CN.n3
    · exact CN.n4
    · exact CN.n5
    · exact CN.n6
  · exact allR_get CN.n7 (by omega) (by omega)

theorem nodeOK_spec {i : Nat} (h : nodeOK i = true) :
    ((nthD (0, 0) xp i).2 = 251 ∧ tabOK ab [(nthD (0, 0) xp i).1] 8330 (nth xn i) = true) ∨
    ((nthD (0, 0) xp i).2 ≠ 251 ∧ stepOK 8330 (nth ab (nthD (0, 0) xp i).1)
      (nth xn (nthD (0, 0) xp i).2) (nth xn i) = true) := by
  unfold nodeOK at h
  cases hb : Nat.beq (nthD (0, 0) xp i).2 251
  · rw [hb] at h
    exact Or.inr ⟨Nat.ne_of_beq_eq_false hb, h⟩
  · rw [hb] at h
    exact Or.inl ⟨Nat.eq_of_beq_eq_true hb, h⟩

theorem spl_nil (i : Nat) : spl [] i = Nat.beq i 251 := rfl

theorem spl_cons (l : Nat) (w : List Nat) (i : Nat) :
    spl (l :: w) i =
      (Nat.blt i 251 && Nat.beq (nthD (0, 0) xp i).1 l && spl w (nthD (0, 0) xp i).2) := rfl

theorem node_code : ∀ (w : List Nat) (i : Nat), spl w i = true → (∀ l ∈ w, l < 4) → w ≠ [] →
    ∀ p < 8330, im (nth xn i) p = act 8330 (wAB a b w) p := by
  intro w
  induction w with
  | nil => intro _ _ _ h; exact absurd rfl h
  | cons l w ih =>
    intro i hs hw _
    rw [spl_cons, Bool.and_eq_true, Bool.and_eq_true] at hs
    obtain ⟨⟨h1, h2⟩, h3⟩ := hs
    have hi : i < 251 := by simpa using h1
    have hl : (nthD (0, 0) xp i).1 = l := Nat.eq_of_beq_eq_true h2
    rcases nodeOK_spec (nodes_all i hi) with ⟨hp, ht⟩ | ⟨hp, hst⟩
    · cases w with
      | nil =>
        intro p hpn
        rw [tabOK_code ht p hpn, hl]
        exact word_code hw p hpn
      | cons l2 w2 =>
        rw [hp, spl_cons] at h3
        have e : Nat.blt 251 251 = false := rfl
        rw [e] at h3
        simp at h3
    · have hw' : w ≠ [] := by
        rintro rfl
        rw [spl_nil] at h3
        exact hp (Nat.eq_of_beq_eq_true h3)
      have ih' := ih _ h3 (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) hw'
      intro p hpn
      rw [stepOK_code hst p hpn, ih' p hpn, hl, ab_code l (hw l List.mem_cons_self) _ (act_lt _ hpn),
        ← act_mul _ _ hpn, wAB, wAB, wprod_cons]

theorem X_code {j : Nat} (hj : j < 133) : CodeOf 8330 (X j) (xs j) := by
  obtain ⟨-, hri, -, -, -, -, -, hri251, -, -, -⟩ := lens_parts
  have hrij : nth ri j < 251 :=
    hri251 _ (by rw [nth_eq]; exact getD_mem (by rw [← lenK_eq, hri]; exact hj) _)
  have hs : spl (W j) (nth ri j) = true := allN_iff.mp CG.spell j hj
  have hne : W j ≠ [] := by
    intro h
    rw [h, spl_nil] at hs
    have := Nat.eq_of_beq_eq_true hs
    omega
  exact node_code (W j) (nth ri j) hs (W_letters hj) hne

theorem lab_R : ∀ g ∈ Rg, ∀ q < 8330, im lb (act 8330 g q) = im lb q := by
  intro g hg
  refine lab_closure (fun q => im lb q) rts (fun s hs q hq => ?_) hg
  simp only [rts, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · have h := Nat.eq_of_beq_eq_true (allN_iff.mp CB.lab0 q hq)
    rw [rg_code 0 (by norm_num) q hq] at h
    exact h
  · have h := Nat.eq_of_beq_eq_true (allN_iff.mp CB.lab1 q hq)
    rw [rg_code 1 (by norm_num) q hq] at h
    exact h

theorem edgeList_eq (x : J) : edgeList rts x = [rt 0, rt 1, (rt 0)⁻¹, (rt 1)⁻¹, x, x⁻¹] := rfl

theorem edgeLK_act {s : Nat} (hs : s < 133) {l : Nat} (hl : l < 6) {q : Nat} (hq : q < 8330) :
    edgeLK rg rgi ab (W s) (X s) l q = act 8330 ((edgeList rts (xs s)).getD l 1) q := by
  rw [edgeList_eq]
  interval_cases l
  · exact rg_code 0 (by norm_num) q hq
  · exact rg_code 1 (by norm_num) q hq
  · exact rgi_code 0 (by norm_num) q hq
  · exact rgi_code 1 (by norm_num) q hq
  · exact X_code hs q hq
  · exact wordInv_code (W_letters hs) q hq

theorem evalEK_act {s : Nat} (hs : s < 133) : ∀ e : List Nat, (∀ l ∈ e, l < 6) → ∀ p < 8330,
    evalEK rg rgi ab (W s) (X s) e p = act 8330 (wprod (edgeList rts (xs s)) e) p := by
  intro e
  induction e with
  | nil =>
    intro _ p hp
    simp only [wprod, List.map_nil, List.prod_nil]
    exact (act_one hp).symm
  | cons l e ih =>
    intro he p hp
    have e1 : evalEK rg rgi ab (W s) (X s) (l :: e) p =
        edgeLK rg rgi ab (W s) (X s) l (evalEK rg rgi ab (W s) (X s) e p) := rfl
    rw [e1, ih (fun l' hl' => he l' (List.mem_cons_of_mem _ hl')) p hp, wprod_cons,
      act_mul _ _ hp]
    exact edgeLK_act hs (he l List.mem_cons_self) (act_lt _ hp)

theorem edge_mem : ∀ ed ∈ edges,
    ed.1 < 133 ∧ ed.2.1 < 133 ∧ xs ed.2.1 ∈ Rg ⊔ Subgroup.zpowers (xs ed.1) := by
  intro ed hed
  have h := allL_iff.mp CI.edgesC ed hed
  unfold edgeOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hs : ed.1 < 133 := by simpa using h1
  have hd : ed.2.1 < 133 := by simpa using h2
  refine ⟨hs, hd, ?_⟩
  have heq : xs ed.2.1 = wprod (edgeList rts (xs ed.1)) ed.2.2 := by
    refine eq_of_base hB hbase fun p hp => ?_
    have := Nat.eq_of_beq_eq_true (allL_iff.mp h4 p hp)
    rw [X_code hd p (hB p hp),
      evalEK_act hs _ (fun l hl => by simpa using allL_iff.mp h3 l hl) p (hB p hp)] at this
    exact this
  rw [heq]
  exact wprod_edge_mem rts (xs ed.1) ed.2.2

theorem inTree : ∀ i < 133, i ≠ 0 →
    ∃ d < 133, (∃ ed ∈ edges, ed.1 = i ∧ ed.2.1 = d) ∧ nth dIn d < nth dIn i := by
  intro i hi hi0
  have h := allN_iff.mp CI.inT i hi
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd (Nat.eq_of_beq_eq_true h) hi0
  · have hmem : nthD (0, 0, []) edges (nth inEdge i) ∈ edges := by
      rw [nthD_eq]
      exact getD_mem (by rw [← lenK_eq]; simpa using h1) _
    exact ⟨_, (edge_mem _ hmem).2.1, ⟨_, hmem, Nat.eq_of_beq_eq_true h2, rfl⟩,
      by simpa using h3⟩

theorem outT_parts : (∀ j ∈ reach, j ≠ 0 → ∃ s ∈ reach,
    (∃ ed ∈ edges, ed.1 = s ∧ ed.2.1 = j) ∧ nth dOut s < nth dOut j) ∧ reach.Nodup ∧
    ∀ j ∈ reach, j < 133 := by
  have h := CI.outT
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun j hj hj0 => ?_, allNeK_nodup h2, fun j hj => by simpa using allL_iff.mp h3 j hj⟩
  have h := allL_iff.mp h1 j hj
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩
  · exact absurd (Nat.eq_of_beq_eq_true h) hj0
  · have hmem : nthD (0, 0, []) edges (nth outEdge j) ∈ edges := by
      rw [nthD_eq]
      exact getD_mem (by rw [← lenK_eq]; simpa using ha) _
    exact ⟨_, memN_iff.mp hc, ⟨_, hmem, rfl, Nat.eq_of_beq_eq_true hb⟩, by simpa using hd⟩

theorem h_all : ∀ j < 133, cnt j j = H j := by
  intro j hj
  refine Nat.eq_of_beq_eq_true ?_
  by_cases h : j < 128
  · refine cover (f := fun j => Nat.beq (cnt j j) (H j)) (i := j) (w := 8) (k := 16)
      (fun t ht => ?_) (by omega)
    interval_cases t
    · exact CH.h0
    · exact CH.h1
    · exact CH.h2
    · exact CH.h3
    · exact CH.h4
    · exact CH.h5
    · exact CH.h6
    · exact CH.h7
    · exact CH.h8
    · exact CH.h9
    · exact CH.h10
    · exact CH.h11
    · exact CH.h12
    · exact CH.h13
    · exact CH.h14
    · exact CH.h15
  · exact allR_get CH.h16 (by omega) (by omega)

theorem p_all : ∀ k < 78, cnt (nthD (0, 0) pairs k).1 (nthD (0, 0) pairs k).2 = 0 := by
  intro k hk
  refine Nat.eq_of_beq_eq_true ?_
  by_cases h : k < 72
  · refine cover (f := fun k => Nat.beq (cnt (nthD (0, 0) pairs k).1 (nthD (0, 0) pairs k).2) 0)
      (i := k) (w := 8) (k := 9) (fun t ht => ?_) (by omega)
    interval_cases t
    · exact CP.p0
    · exact CP.p1
    · exact CP.p2
    · exact CP.p3
    · exact CP.p4
    · exact CP.p5
    · exact CP.p6
    · exact CP.p7
    · exact CP.p8
  · exact allR_get CP.p9 (by omega) (by omega)

theorem i_all : ∀ j < 133,
    Nat.add (Nat.mul (invK 8330 lb sel (X j)) 8192) (H j) = nth IV j := by
  intro j hj
  refine Nat.eq_of_beq_eq_true ?_
  by_cases h : j < 96
  · refine cover (f := fun j => Nat.beq (Nat.add (Nat.mul (invK 8330 lb sel (X j)) 8192) (H j))
      (nth IV j)) (i := j) (w := 32) (k := 3) (fun t ht => ?_) (by omega)
    interval_cases t
    · exact CI.i0
    · exact CI.i1
    · exact CI.i2
  · exact allR_get CI.i3 (by omega) (by omega)

theorem massAll_eq : massAll = ((List.range 133).map fun j => 6174 * (6174 / H j)).sum := by
  have key : ∀ k, Nat.rec (motive := fun _ => Nat) 0
      (fun j ih => Nat.add (Nat.mul 6174 (Nat.div 6174 (H j))) ih) k =
      ((List.range k).map fun j => 6174 * (6174 / H j)).sum := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ← ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Nat.add_comm _ _
  exact key 133

theorem listing : (∀ g, g ∈ Rg ↔ g ∈ prods Gs) ∧ Nat.card Rg = 6174 := by
  classical
  obtain ⟨-, -, h3, -, -, -, -, -, -, -, -⟩ := lens_parts
  obtain ⟨hlen, -⟩ := ordT_sound hLG (by norm_num : 2 < 8330) (by norm_num : 0 < 8330) hB
    (by norm_num) ord
  have hne : prods Gs ≠ [] := fun h => by rw [h] at hlen; simp at hlen
  have hlevne : ∀ {Ls : List (List J)}, prods Ls ≠ [] → ∀ L ∈ Ls, L ≠ [] := by
    intro Ls
    induction Ls with
    | nil => intro _ L hL; exact absurd hL List.not_mem_nil
    | cons L Ls ih =>
      intro h L' hL'
      rw [prods_cons] at h
      rcases List.mem_cons.mp hL' with rfl | hL'
      · rintro rfl
        exact h rfl
      · refine ih (fun h0 => h ?_) L' hL'
        rw [h0]
        simp
  have h1 : ∀ L ∈ Gs, L.head? = some 1 := by
    intro L hL
    have hL0 := hlevne hne L hL
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hL
    generalize (lv.getD l []).length = m at hL0 ⊢
    cases m with
    | zero => exact absurd rfl hL0
    | succ m => simp [List.range_succ_eq_map]
  have hlev : ∀ L ∈ Gs, ∀ u ∈ L, u ∈ Subgroup.closure {x | x ∈ rts} := by
    intro L hL u hu
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hL
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hu
    exact Subgroup.pow_mem _ (lg_mem l) k
  have hcl : ∀ s ∈ rts, ∃ S, CodeOf 8330 S s ∧ cntT S 6174 C Q2 RW lv (2 :: 0 :: B) = 6174 := by
    intro s hs
    simp only [rts, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨nth rg 0, rg_code 0 (by norm_num), Nat.eq_of_beq_eq_true CB.cl0⟩
    · exact ⟨nth rg 1, rg_code 1 (by norm_num), Nat.eq_of_beq_eq_true CB.cl1⟩
  exact prods_closure hLG (by norm_num) (by norm_num) hB (by norm_num) (by norm_num) hbase ord h1
    rts hlev hcl

theorem prods_nodup : (prods Gs).Nodup := by
  obtain ⟨hlen, hk⟩ := ordT_sound hLG (by norm_num : 2 < 8330) (by norm_num : 0 < 8330) hB
    (by norm_num) ord
  rw [List.nodup_iff_injective_get]
  intro i j hij
  apply Fin.ext
  have hi := (hk i (by rw [← hlen]; exact i.2)).1
  have hj := (hk j (by rw [← hlen]; exact j.2)).1
  rw [List.getD_eq_getElem _ _ i.2] at hi
  rw [List.getD_eq_getElem _ _ j.2] at hj
  have e : (prods Gs)[i.1] = (prods Gs)[j.1] := by simpa using hij
  rw [e] at hi
  exact hi.symm.trans hj

theorem cnt_eq_cntT {i j : Nat} (hj : j < 133) :
    cnt i j = cntT (X i) 6174 C Q2 RW lv ((2 :: 0 :: B).map (act 8330 (xs j)⁻¹)) := by
  have hpts : wordInvL ab (W j) pts = (2 :: 0 :: B).map (act 8330 (xs j)⁻¹) := by
    rw [wordInvL_eq]
    refine List.map_congr_left fun p hp => wordInv_code (W_letters hj) p ?_
    simp only [pts, B, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  unfold cnt
  rw [hpts]

theorem maximal :
    ∃ R : Subgroup J, Nat.card R = 6174 ∧ ∀ Y : Subgroup J, R ≤ Y → Y = R ∨ Y = ⊤ := by
  classical
  obtain ⟨hout, hnd, hlt⟩ := outT_parts
  have hcnt := fun {i j : Nat} (hi : i < 133) (hj : j < 133) =>
    (cnt_eq_cntT (i := i) hj).trans (cntT_eq hLG (by norm_num) (by norm_num) hB (by norm_num)
      (by norm_num) hbase ord (X_code hi) (xs j))
  have hst := fun {j : Nat} (hj : j < 133) =>
    (card_stab_eq Rg (prods Gs) prods_nodup listing.1 (xs j)).trans ((hcnt hj hj).symm.trans
      (h_all j hj))
  have hm := CI.mass
  simp only [Bool.and_eq_true] at hm
  have hbig : Nat.card J < 2 * (reach.map fun j => 6174 * (6174 / H j)).sum := by
    have h := hm.1
    rw [Nat.blt_eq] at h
    rw [CFSG.Sporadic.He.card_J, ← massK_eq 6174 H reach]
    exact h
  have htot : Nat.card J ≤ ((List.range 133).map fun j => 6174 * (6174 / H j)).sum + 6174 := by
    have h := hm.2
    rw [Nat.ble_eq] at h
    rw [CFSG.Sporadic.He.card_J, ← massAll_eq]
    exact h
  refine ⟨Rg, listing.2, maximal_of_masses Rg 6174 listing.2 xs 133 H (fun j hj => (hst hj).le)
    (fun i hi j hj hij hx => ?_) 0 (fun s d => ∃ ed ∈ edges, ed.1 = s ∧ ed.2.1 = d)
    (fun s d ⟨ed, hed, h1, h2⟩ => h1 ▸ h2 ▸ (edge_mem ed hed).2.2) (nth dIn) (nth dOut) inTree
    reach hlt hnd hout hbig htot⟩
  have h := allN_iff.mp (allN_iff.mp CI.dist j hj) i hij
  by_cases hiv : nth IV i = nth IV j
  · rw [hiv, Nat.beq_refl] at h
    have hm : memP i j pairs = true := by simpa using h
    obtain ⟨k, hk, hpk⟩ := memP_spec hm
    have hk78 : k < 78 := by
      rw [← Nat.eq_of_beq_eq_true CG.npairs, lenK_eq]
      exact hk
    have h0 := p_all k hk78
    rw [nthD_eq, hpk] at h0
    exact not_mem_of_count_zero Rg (prods Gs) listing.1 ((hcnt hi hj).symm.trans h0) hx
  · apply hiv
    have hinv := invK_eq Rg sel lab_R (X_code hi) (X_code hj) hx
    have hHe : H j = H i := (hst hj).symm.trans ((card_stab_of_mem Rg hx).trans (hst hi))
    rw [← i_all i hi, ← i_all j hj, hinv, hHe]

end He

end CFSG.KD.He31064

end
