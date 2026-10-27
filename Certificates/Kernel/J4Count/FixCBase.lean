
module

public import Certificates.Kernel.J4Count.FixCChecks
public import Certificates.Kernel.J4Count.FixZBase
public import CFSG.Certificates.Kernel.J4FixCSoundBase
public import CFSG.Sporadic.J4.Struct.FixCount
public import Certificates.Kernel.J4Hub.Card

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixC

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.KC.J4FixC CFSG.KD.J4FixC CFSG.KS.SporSch.C11 CFSG.Sporadic.GLQ
open CFSG.Sporadic.SmallF2.Native (vecMulN)
open CFSG.KC.J4Count (combo decode BS PS)
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4NoCK
open CertificateChecks.KernelSporSch.J4Eta CertificateChecks.KernelSporSch.J4NoCP

section Generic

variable {Λ : Type*} [Group Λ] [Finite Λ]

theorem card_filter_exists_le [Fintype Λ] [DecidableEq Λ] (reps : List Λ) (T : Λ → Λ → Prop)
    [∀ r t, Decidable (T r t)] :
    (Finset.univ.filter fun s => ∃ r ∈ reps, T r s).card ≤
      (reps.map fun r => (Finset.univ.filter (T r)).card).sum := by
  induction reps with
  | nil => simp
  | cons r rs ih =>
    have e : (Finset.univ.filter fun s => ∃ r' ∈ r :: rs, T r' s) =
        Finset.univ.filter (T r) ∪ Finset.univ.filter fun s => ∃ r' ∈ rs, T r' s := by
      ext s
      simp
    rw [e, List.map_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem card_le_sum_classes {p : ℕ} [Fact p.Prime] (P : Sylow p Λ) (S : Λ → Prop)
    (hS : ∀ s, S s → ∀ g : Λ, S (g⁻¹ * s * g)) (hp : ∀ s, S s → s ^ p = 1) (reps : List Λ)
    (hfus : ∀ x ∈ (P : Subgroup Λ), S x → ∃ r ∈ reps, IsConj x r) :
    Nat.card {s // S s} ≤ (reps.map fun r => Nat.card {t // IsConj r t}).sum := by
  classical
  have : Fintype Λ := Fintype.ofFinite Λ
  have key : ∀ s, S s → ∃ r ∈ reps, IsConj r s := by
    intro s hs
    have hpg : IsPGroup p (Subgroup.zpowers s) := by
      intro g
      refine ⟨1, Subtype.ext ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, hp s hs, one_zpow]
    obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Λ P Q
    have hsQ : s ∈ (Q : Subgroup Λ) := hQ (Subgroup.mem_zpowers s)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hsQ
    obtain ⟨x', hxP, hx⟩ := hsQ
    have hx' : g * x' * g⁻¹ = s := hx
    have hxs : x' = g⁻¹ * s * g := by rw [← hx']; group
    have hSx : S x' := by rw [hxs]; exact hS s hs g
    obtain ⟨r, hr, hxr⟩ := hfus x' hxP hSx
    exact ⟨r, hr, hxr.symm.trans (isConj_iff.2 ⟨g, hx'⟩)⟩
  calc Nat.card {s // S s} = (Finset.univ.filter S).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ (Finset.univ.filter fun s => ∃ r ∈ reps, IsConj r s).card :=
        Finset.card_le_card fun s hs => by
          rw [Finset.mem_filter] at hs ⊢
          exact ⟨hs.1, key s hs.2⟩
    _ ≤ (reps.map fun r => (Finset.univ.filter (IsConj r)).card).sum :=
        card_filter_exists_le reps IsConj
    _ = (reps.map fun r => Nat.card {t // IsConj r t}).sum := by
        congr 1
        refine List.map_congr_left fun r _ => ?_
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_class_le (r : Λ) {m : ℕ} (hm : 0 < m)
    (h : m ≤ Nat.card (Subgroup.centralizer ({r} : Set Λ))) :
    Nat.card {t // IsConj r t} ≤ Nat.card Λ / m := by
  have e := CFSG.Sporadic.J4.Struct.card_centralizer_mul_card_conj r
  have hC : 0 < Nat.card (Subgroup.centralizer ({r} : Set Λ)) := Nat.card_pos
  rw [Nat.le_div_iff_mul_le hm, ← e, mul_comm]
  exact Nat.mul_le_mul_right _ h

theorem sum_classes_le (n : ℕ) (f : ℕ → Λ) (m : ℕ → ℕ) (hm : ∀ r < n, 0 < m r)
    (h : ∀ r < n, m r ≤ Nat.card (Subgroup.centralizer ({f r} : Set Λ))) :
    (((List.range n).map f).map fun r => Nat.card {t // IsConj r t}).sum ≤
      ((List.range n).map fun r => Nat.card Λ / m r).sum := by
  rw [List.map_map]
  refine List.sum_le_sum fun r hr => ?_
  have hr' := List.mem_range.1 hr
  exact card_class_le (f r) (hm r hr') (h r hr')

theorem one_mem_of_closed {S : Set Λ} {a : Λ} (ha : a ∈ S)
    (hmul : ∀ u ∈ S, ∀ w ∈ S, u * w ∈ S) : (1 : Λ) ∈ S := by
  have hpow : ∀ n : ℕ, a ^ (n + 1) ∈ S := fun n => by
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      rw [pow_succ]
      exact hmul _ ih _ ha
  have h := hpow (orderOf a - 1)
  rwa [Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one] at h

theorem closure_coe_eq {S : Set Λ} {a : Λ} (ha : a ∈ S) (hmul : ∀ u ∈ S, ∀ w ∈ S, u * w ∈ S) :
    ((Subgroup.closure S : Subgroup Λ) : Set Λ) = S := by
  refine Set.Subset.antisymm (fun g hg => ?_) Subgroup.subset_closure
  have hg' : g ∈ Submonoid.closure S := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  let M : Submonoid Λ := ⟨⟨S, fun {u w} hu hw => hmul u hu w hw⟩, one_mem_of_closed ha hmul⟩
  exact (Submonoid.closure_le (S := M)).2 (fun _ h => h) hg'

end Generic

section Words

theorem letM_eq (c : ℕ) : letM (R 1) (R 10) (R 2) (R 11) c =
    if c = 0 then R 1 else if c = 1 then R 10 else if c = 2 then R 2 else R 11 := by
  rcases c with _ | _ | _ | c <;> rfl

@[expose] noncomputable def genE (g : List ℕ × ℕ) : J := signedWord x y (toI g.1) * η g.2

theorem genE_mem_H (g : List ℕ × ℕ) : genE g ∈ H :=
  H.mul_mem (K_le_H (signedWord_mem_K _)) (N_le_H (η_mem_N _))

noncomputable abbrev Lj (l : ℕ) : Subgroup J := H ⊓ MulAction.stabilizer J (qv l)

@[expose] noncomputable def gsl (l : ℕ) : List J := (GN l).map genE

@[expose] noncomputable def WE (l : ℕ) (w : List ℕ) : J := wordE (gsl l) w

theorem nth_map_of_lt {α β : Type} (f : α → β) (d : β) (d' : α) {l : List α} {i : ℕ}
    (hi : i < l.length) : nth d (l.map f) i = f (nth d' l i) := by
  rw [nth_eq, nth_eq, List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]

theorem nth_map_ge {α β : Type} (f : α → β) (d : β) (l : List α) {i : ℕ} (hi : l.length ≤ i) :
    nth d (l.map f) i = d := by
  rw [nth_eq, List.getD_eq_default _ _ (by simpa using hi)]

theorem nth_mem_of_lt {α : Type} (d : α) {l : List α} {i : ℕ} (hi : i < l.length) :
    nth d l i ∈ l := by
  rw [nth_eq, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

end Words

section Conj

end Conj

section Local

theorem finite_J : Finite J := CertificateChecks.KernelJ4Hub.finite_J

@[expose] noncomputable def PE (l : ℕ) : List J := (nth [] PW l).map (WE l)

theorem PE_length {l : ℕ} (hl : l < 7) : (PE l).length = nth 0 NP l := by
  have h := CFSG.KS.allN_spec plen_ok l hl
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  rw [← Nat.eq_of_beq_eq_true h.1, PE, PL, List.length_map, List.length_map]

@[expose] noncomputable def PJ (l : ℕ) : Subgroup J := Subgroup.closure {g | g ∈ PE l}

@[expose] noncomputable def RE (l r : ℕ) : J := WE l (nth [] (nth [] RW l) r)

@[expose] noncomputable def CE (l r : ℕ) : List J := (CWL l r).map (WE l)

@[expose] noncomputable def TE (l r j : ℕ) : J := wordE (CE l r) (nth [] (nth [] (nth [] TW l) r) j)

theorem RL_nth {l r : ℕ} (hr : r < NR l) : nth 0 (RL l) r = EV l (nth [] (nth [] RW l) r) :=
  nth_map_of_lt _ _ _ hr

theorem TL_length {l r : ℕ} (hl : l < 7) (hr : r < NR l) :
    (TL l r).length = nth 0 (nth [] NT l) r :=
  Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec (CFSG.KS.allN_spec tlen_ok l hl) r hr)

theorem TL_ne {l r : ℕ} (hl : l < 7) (hr : r < NR l) {j j' : ℕ} (hj : j < (TL l r).length)
    (hj' : j' < (TL l r).length) (hne : j ≠ j') :
    unpack11 (pcK (nth 0 (TL l r) j)) ≠ unpack11 (pcK (nth 0 (TL l r) j')) := by
  obtain ⟨hc, hs⟩ := sortedK_spec (CFSG.KS.allN_spec (CFSG.KS.allN_spec sorted_ok l hl) r hr)
  have key : ∀ {a b : ℕ}, a < (TL l r).length → b < (TL l r).length → a < b →
      unpack11 (pcK (nth 0 (TL l r) a)) ≠ unpack11 (pcK (nth 0 (TL l r) b)) := by
    intro a b ha hb hab
    rw [nth_eq, nth_eq, List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
    have hlt := List.pairwise_iff_getElem.1 hs a b ha hb hab
    refine ne_sound ?_
    rw [bAnd_eq, bAnd_eq, (hc _ (List.getElem_mem ha)).1, (hc _ (List.getElem_mem hb)).1]
    simp only [Bool.true_and, Bool.not_eq_true']
    exact Bool.eq_false_iff.2 fun h => Nat.ne_of_lt hlt (Nat.eq_of_beq_eq_true h)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key hj hj' h
  · exact fun e => key hj' hj h e.symm

end Local

section Bound

theorem card_le_of_injOn {G X : Type*} [Group G] [Finite G] (S : Subgroup G) (s : Finset X)
    (f : X → G) (hmem : ∀ q ∈ s, f q ∈ S) (hinj : Set.InjOn f s) : s.card ≤ Nat.card S := by
  classical
  have h : (s.image f).card = s.card := Finset.card_image_of_injOn hinj
  rw [← h, ← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective (fun z => ⟨z.1, ?_⟩) (fun a b e => ?_)
  · obtain ⟨q, hq, e⟩ := Finset.mem_image.1 z.2
    rw [← e]
    exact hmem q hq
  · have e' := congrArg Subtype.val e
    exact Subtype.ext e'

@[expose] noncomputable def AF (l r : ℕ) : Finset ℕ :=
  (Finset.range 2048).filter fun a =>
    bAnd(Nat.beq (combo (nth [] BS l) (decode (nth [] PS l) a)) a,
      Nat.beq (appK (pcK (nth 0 (RL l) r)) a) a) = true

theorem AF_card {l r : ℕ} (hl : l < 7) (hr : r < NR l) : (AF l r).card = nth 0 (nth [] NA l) r := by
  rw [AF, ← cntN_eq]
  exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec (CFSG.KS.allN_spec cnt_ok l hl) r hr)

theorem card_centralizer_sub (L : Subgroup J) (g : L) :
    Nat.card (Subgroup.centralizer ({g} : Set L)) =
      Nat.card ↥(L ⊓ Subgroup.centralizer {(g : J)}) :=
  Nat.card_congr
    { toFun := fun s => ⟨s.1.1, Subgroup.mem_inf.2 ⟨s.1.2, Subgroup.mem_centralizer_singleton_iff.2
        (by simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 s.2))⟩⟩
      invFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.1 s.2).1⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (by simpa using
          Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 s.2).2))⟩
      left_inv := fun s => Subtype.ext (Subtype.ext rfl)
      right_inv := fun s => Subtype.ext rfl }

theorem centralizer_one : Subgroup.centralizer ({1} : Set J) = ⊤ := by
  ext g
  simp [Subgroup.mem_centralizer_singleton_iff]

theorem card_Lj_stab (l : ℕ) : Nat.card (Lj l) = Nat.card (MulAction.stabilizer H (qv l)) :=
  Nat.card_congr
    { toFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.1 s.2).1⟩, (Subgroup.mem_inf.1 s.2).2⟩
      invFun := fun s => ⟨s.1.1, Subgroup.mem_inf.2 ⟨s.1.2, s.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Bound

section Final

@[expose] def FB : List ℕ := [1, 0, 0, 480, 120, 60, 76]

end Final

end CertificateChecks.KernelJ4Count.FixC

end
