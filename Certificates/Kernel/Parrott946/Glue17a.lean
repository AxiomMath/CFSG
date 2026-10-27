
module

public import Certificates.Kernel.Parrott946.Glue17
public import CFSG.Certificates.Kernel.Parrott946.CliqueSound
public import CFSG.RankThree.GF2n.Parrott.QA45ListGroupsBase

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.Certificates.Kernel.PkCV
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups
  CertificateChecks.KernelA45 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

theorem nodup_of_card {L : List P45} {H : Subgroup P45} (hL : ∀ x, x ∈ L ↔ x ∈ H)
    (hlen : L.length = Nat.card H) : L.Nodup := by
  classical
  have hc : L.toFinset.card = Nat.card H := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => List.mem_toFinset.trans (hL x))
  rw [List.card_toFinset] at hc
  exact List.dedup_eq_self.1 ((List.dedup_sublist L).eq_of_length (by rw [hc, hlen]))

theorem listFacts_of {L gs : List P45} {H : Subgroup P45} (hL : ∀ x, x ∈ L ↔ x ∈ H)
    (hn : L.Nodup) (hg : ∀ g ∈ gs, g ∈ H) (hA : H ≤ A) : ListGroupFacts L gs where
  nodup := hn
  one_mem := (hL 1).2 H.one_mem
  mul_closed := List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun y hy =>
    decide_eq_true ((hL _).2 (H.mul_mem ((hL x).1 hx) ((hL y).1 hy)))
  inv_closed := List.all_eq_true.2 fun x hx => decide_eq_true ((hL _).2 (H.inv_mem ((hL x).1 hx)))
  gens_mem := List.all_eq_true.2 fun g hg' => decide_eq_true ((hL g).2 (hg g hg'))
  in_A := List.all_eq_true.2 fun x hx => (mem_iff_sift QA45 QA45_ok x).1 (hA ((hL x).1 hx))

theorem prodSpan_cons (g : P45) (gs : List P45) :
    prodSpan (g :: gs) = prodSpan gs ++ (prodSpan gs).map (g * ·) := rfl

theorem prodSpan_mem (H : Subgroup P45) : ∀ {gs : List P45}, (∀ g ∈ gs, g ∈ H) →
    ∀ x ∈ prodSpan gs, x ∈ H
  | [], _, x, hx => by
    have e : x = 1 := by simpa [prodSpan] using hx
    rw [e]
    exact H.one_mem
  | g :: gs, hg, x, hx => by
    rw [prodSpan_cons, List.mem_append, List.mem_map] at hx
    have ih := prodSpan_mem H (gs := gs) fun y hy => hg y (List.mem_cons_of_mem g hy)
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ih x hx
    · exact H.mul_mem (hg g List.mem_cons_self) (ih y hy)

theorem prep_pid : PRep 45 6 (pidn 45 6) 1 := prep_pidn (by norm_num) (by norm_num)

theorem spanK_prep {Ls : List ℕ} {gs : List P45} (h : List.Forall₂ (PRep 45 6) Ls gs) :
    List.Forall₂ (PRep 45 6) (spanK 45 6 (pidn 45 6) Ls) (prodSpan gs) := by
  induction h with
  | nil => exact List.Forall₂.cons prep_pid List.Forall₂.nil
  | @cons P g Ls gs hP _ ih =>
    have e : spanK 45 6 (pidn 45 6) (P :: Ls) = appK (spanK 45 6 (pidn 45 6) Ls)
        (mapK (pcomp 45 6 (mask 6) P) (spanK 45 6 (pidn 45 6) Ls)) := rfl
    rw [e, appK_eq, mapK_eq, prodSpan_cons]
    refine List.rel_append ih ?_
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact ih.imp fun _ _ hab => prep_pcomp hn45 hP hab

theorem f2_mem_left {R : ℕ → P45 → Prop} {l1 : List ℕ} {l2 : List P45}
    (h : List.Forall₂ R l1 l2) {a : ℕ} (ha : a ∈ l1) : ∃ b ∈ l2, R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem f2_mem_right {R : ℕ → P45 → Prop} {l1 : List ℕ} {l2 : List P45}
    (h : List.Forall₂ R l1 l2) {b : P45} (hb : b ∈ l2) : ∃ a ∈ l1, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

@[expose] def g0 (k : ℕ) : P45 := T0gens.getD k 1

abbrev T0g : Subgroup P45 := closure (g0 '' {k | k < 6})

theorem prep_g0 : ∀ k < 6, PRep 45 6 (T0Z.G k) (g0 k) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, -⟩ := c17_binds
  intro k hk
  interval_cases k
  · rw [b0]
    exact prep_u
  · rw [b1]
    exact prep_v
  · rw [b2]
    exact prep_a1
  · rw [b3]
    exact prep_b1
  · rw [b4]
    exact prep_a2
  · rw [b5]
    exact prep_b2

theorem g0_mem {k : ℕ} (hk : k < 6) : g0 k ∈ T0g := subset_closure ⟨k, hk, rfl⟩

theorem T0g_le_A : T0g ≤ A := by
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < 6 := hk
  interval_cases k
  · exact u_memA
  · exact v_memA
  · exact alpha1_memA
  · exact beta1_memA
  · exact alpha2_memA
  · exact beta2_memA

theorem t0_enum : ∃ c : ℕ → P45, (∀ i < 128, PRep 45 6 (T0Z.T i) (c i) ∧ c i ∈ T0g) ∧
    (∀ y ∈ T0g, ∃ i < 128, c i = y) ∧ Nat.card T0g = 128 := by
  have hid : PRep 45 6 (T0Z.T 0) 1 := by
    rw [c17_ids.1]
    exact prep_pid
  obtain ⟨c, hc0, hc, hmem, hcl', hinj⟩ :=
    leftOrb_reps (g := g0) hn45 prep_g0 T0Z.cl T0Z.tr (by decide) hid ps_lt T0Z.k
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) (fun _ _ h => h) g0 c
    ⟨0, by decide, hc0⟩ hmem hcl' hinj
  exact ⟨c, fun i hi => ⟨hc i hi, hmem i hi⟩, fun y hy => hall y hy, hcard⟩

theorem card_T0g : Nat.card T0g = 128 := by
  obtain ⟨-, -, -, h⟩ := t0_enum
  exact h

theorem I_lt : allL D17.I (fun _ c => Nat.blt c (2 ^ 270)) 0 = true := by decide +kernel

theorem len_I : D17.I.length = 43 := by
  rw [← lenK_eq]
  exact c17_inv.2.1

theorem allL_mem {L : List ℕ} {f : ℕ → ℕ → Bool} (h : allL L f 0 = true) {x : ℕ} (hx : x ∈ L) :
    ∃ j, f j x = true := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  have := allL_spec h j hj
  rw [Nat.zero_add, List.getD_eq_getElem _ _ hj] at this
  exact ⟨j, this⟩

set_option exponentiation.threshold 300 in
theorem iE_eq {j : ℕ} (hj : j < 43) : iE j = D17.I.getD j 0 := by
  rw [iE, ← c17_inv.2.2.1]
  refine lane_packL (fun c hc => ?_) (by rw [len_I]; exact hj)
  obtain ⟨_, h⟩ := allL_mem I_lt hc
  exact Nat.blt_eq.mp h

theorem prep_iE {j : ℕ} (hj : j < 43) :
    ∃ x, PRep 45 6 (iE j) x ∧ x ∈ T0g ∧ x * x = 1 ∧ x ≠ 1 := by
  have h := allL_spec c17_inv.2.2.2.1 j (by rw [len_I]; exact hj)
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨i, hi, e⟩ := memK_spec h.2
  obtain ⟨c, hc, -⟩ := t0_enum
  have hp : PRep 45 6 (iE j) (c i) := by
    rw [iE_eq hj, ← e]
    exact (hc i hi).1
  exact ⟨c i, hp, (hc i hi).2, (inv_iff_isInvK hp).1 (by rw [← iE_eq hj] at h; exact h.1)⟩

theorem t_mem_T0g : t ∈ T0g := by
  obtain ⟨x, hx, hxT, -⟩ := prep_iE (j := 41) (by norm_num)
  rw [c17_gens.2.2.2.1] at hx
  rw [prep_eq prep_t hx]
  exact hxT

theorem T0list_eq : T0list () = prodSpan [u, v, t, alpha1, beta1, alpha2, beta2] := by
  rw [T0list, tabList_eq, tabList_eq]

theorem t0_set : ∀ x, x ∈ T0list () ↔ x ∈ T0g := by
  have h7 : List.Forall₂ (PRep 45 6) [wE 1, wE 2, wE 0, wE 5, wE 6, wE 7, wE 8]
      [u, v, t, alpha1, beta1, alpha2, beta2] :=
    .cons prep_u (.cons prep_v (.cons prep_t (.cons prep_a1 (.cons prep_b1 (.cons prep_a2
      (.cons prep_b2 .nil))))))
  have hs := spanK_prep h7
  obtain ⟨c, hc, hall, -⟩ := t0_enum
  intro x
  rw [T0list_eq]
  constructor
  · refine prodSpan_mem T0g ?_ x
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g0_mem (k := 0) (by norm_num)
    · exact g0_mem (k := 1) (by norm_num)
    · exact t_mem_T0g
    · exact g0_mem (k := 2) (by norm_num)
    · exact g0_mem (k := 3) (by norm_num)
    · exact g0_mem (k := 4) (by norm_num)
    · exact g0_mem (k := 5) (by norm_num)
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hall x hx
    obtain ⟨P, hP, e⟩ := idxCoverK_spec c17_t0span hi
    obtain ⟨y, hy, hPy⟩ := f2_mem_left hs hP
    rw [← e] at hPy
    rw [prep_eq (hc i hi).1 hPy]
    exact hy

theorem t0_group : ListGroupFacts (T0list ()) T0gens := by
  refine listFacts_of t0_set (nodup_of_card t0_set (by rw [length_T0list, card_T0g]; rfl))
    ?_ T0g_le_A
  intro g hg
  simp only [T0gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact g0_mem (k := 0) (by norm_num)
  · exact g0_mem (k := 1) (by norm_num)
  · exact g0_mem (k := 2) (by norm_num)
  · exact g0_mem (k := 3) (by norm_num)
  · exact g0_mem (k := 4) (by norm_num)
  · exact g0_mem (k := 5) (by norm_num)

end CertificateChecks.Parrott946

end
