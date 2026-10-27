
module

public import Certificates.Kernel.Parrott946.Glue
public import Certificates.Kernel.Parrott946.Checks16
public import Certificates.Kernel.Parrott946.Checks16b
public import Certificates.Kernel.J4Q.ListAux

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

theorem prep_ev (a : CV 45) : PRep 45 6 a.1 (ev a) := by
  intro x
  rw [ev_apply]
  change pg 6 (mask 6) a.1 x = pg (wC 45) (mask (wC 45)) a.1 x
  rw [wC45]

theorem cOf_ev (a : CV 45) : cOf (ev a) = a := ev_injective (ev_cOf (ev a))

theorem cOf_mul (x y : P45) : cOf (x * y) = cOf x * cOf y :=
  ev_injective (by rw [ev_cOf, ev_mul, ev_cOf, ev_cOf])

theorem cOf_inv (x : P45) : cOf x⁻¹ = (cOf x)⁻¹ := ev_injective (by rw [ev_cOf, ev_inv, ev_cOf])

theorem cOf_one : cOf (1 : P45) = 1 := ev_injective (by rw [ev_cOf, ev_one])

theorem cOf_inj {x y : P45} (h : cOf x = cOf y) : x = y := by
  rw [← ev_cOf x, h, ev_cOf]

theorem eq_of_beq {a b : CV 45} (h : Nat.beq a.1 b.1 = true) : a = b :=
  Subtype.ext (Nat.eq_of_beq_eq_true h)

theorem mul_eq_of_eq22 {P Q R S : ℕ} {a b c d : P45} (hP : PRep 45 6 P a) (hQ : PRep 45 6 Q b)
    (hR : PRep 45 6 R c) (hS : PRep 45 6 S d) (h : eq22 45 6 (mask 6) P Q R S = true) :
    a * b = c * d := by
  unfold eq22 at h
  rw [allN_iff] at h
  refine Equiv.ext fun x => Fin.ext ?_
  have := Nat.eq_of_beq_eq_true (h x x.2)
  rw [hQ x, hP (b x), hS x, hR (d x)] at this
  exact this

theorem closeStep_map (S St : List (CV 45)) :
    closeStep (S.map ev) (St.map ev) = (closeStepC S St).map ev := by
  unfold closeStep closeStepC
  rw [← CertificateChecks.KernelJ4Q.eraseDups_map_inj _ _ le_rfl
    (fun x _ y _ h => ev_injective h)]
  congr 1
  simp [List.product, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, ev_mul]

theorem closeFuel_map (St : List (CV 45)) :
    ∀ (k : ℕ) (S : List (CV 45)), closeFuel (St.map ev) k (S.map ev) = (closeFuelC St k S).map ev
  | 0, _ => rfl
  | k + 1, S => by
    change closeFuel _ k (closeStep _ _) = (closeFuelC St k (closeStepC S St)).map ev
    rw [closeStep_map, closeFuel_map St k]

theorem o3Steps_eq : o3StepsC.map ev = o3Steps := by
  simp [o3StepsC, List.map_map, Function.comp_def, ev_cOf]

theorem O3_eq : O3 () = O3C.map ev := by
  have h1 : ([1] : List P45) = [(1 : CV 45)].map ev := by rw [List.map_singleton, ev_one]
  change closeFuel o3Steps 6 [1] = (closeFuelC o3StepsC 6 [1]).map ev
  rw [← o3Steps_eq, h1, closeFuel_map]

theorem mem_O3 {x : P45} : x ∈ O3 () ↔ cOf x ∈ O3C := by
  rw [O3_eq, ← mem_map_ev, ev_cOf]

theorem ev_mem_O3 {a : CV 45} (h : a ∈ O3C) : ev a ∈ O3 () := by
  rw [mem_O3, cOf_ev]
  exact h

theorem o3_mul {x y : P45} (hx : x ∈ O3 ()) (hy : y ∈ O3 ()) : x * y ∈ O3 () := by
  rw [mem_O3] at hx hy ⊢
  have := List.all_eq_true.1 (List.all_eq_true.1 o3c_facts.2.2.2.1 _ hx) _ hy
  rw [cOf_mul]
  exact of_decide_eq_true this

theorem o3_inv {x : P45} (hx : x ∈ O3 ()) : x⁻¹ ∈ O3 () := by
  rw [mem_O3] at hx ⊢
  rw [cOf_inv]
  exact of_decide_eq_true (List.all_eq_true.1 o3c_facts.2.2.2.2.1 _ hx)

theorem o3_one : (1 : P45) ∈ O3 () := by
  rw [mem_O3, cOf_one]
  exact o3c_facts.2.2.1

theorem o3_pow {x : P45} (hx : x ∈ O3 ()) : x ^ 3 = 1 := by
  rw [mem_O3] at hx
  have := List.all_eq_true.1 o3c_facts.2.2.2.2.2.2.2.2.2.2.1 _ hx
  rw [powOneC_eq] at this
  rw [← ev_cOf x, ev_pow', of_decide_eq_true this, ev_one]

theorem o3_comm_s1 {x : P45} (hx : x ∈ O3 ()) : x * sigma1 = sigma1 * x := by
  rw [mem_O3] at hx
  have := List.all_eq_true.1 o3c_facts.2.2.2.2.2.2.2.2.2.2.2.2 _ hx
  rw [eq22C_eq] at this
  apply cOf_inj
  rw [cOf_mul, cOf_mul]
  exact of_decide_eq_true this

theorem s1_mem_O3 : sigma1 ∈ O3 () := mem_O3.2 o3c_facts.2.2.2.2.2.2.1

theorem o3b_mem_O3 : o3b ∈ O3 () := mem_O3.2 o3c_facts.2.2.2.2.2.2.2.1

theorem o3c_mem_O3 : o3c ∈ O3 () := mem_O3.2 o3c_facts.2.2.2.2.2.2.2.2.1

theorem s12i_not_mem_O3 : sigma1 * sigma2⁻¹ ∉ O3 () := by
  rw [mem_O3]
  exact o3c_facts.2.2.2.2.2.2.2.2.2.1

theorem o3_fixed' : closeStep (O3 ()) o3Steps = O3 () := by
  rw [O3_eq, ← o3Steps_eq, closeStep_map, o3c_facts.2.2.2.2.2.1]

theorem o3_noncomm : ∃ x ∈ O3 (), ∃ y ∈ O3 (), x * y ≠ y * x := by
  obtain ⟨a, ha, h⟩ := List.any_eq_true.1 o3c_facts.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨b, hb, h⟩ := List.any_eq_true.1 h
  rw [eq22C_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  refine ⟨ev a, ev_mem_O3 ha, ev b, ev_mem_O3 hb, fun e => h ?_⟩
  apply ev_injective
  rw [ev_mul, ev_mul, e]

theorem closeFuel_le (H : Subgroup P45) (St : List P45) (hSt : ∀ s ∈ St, s ∈ H) :
    ∀ (k : ℕ) (S : List P45), (∀ x ∈ S, x ∈ H) → ∀ x ∈ closeFuel St k S, x ∈ H
  | 0, _, hS => hS
  | k + 1, S, hS => by
    refine closeFuel_le H St hSt k (closeStep S St) ?_
    intro x hx
    rw [closeStep, List.mem_eraseDups, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hS x hx
    · obtain ⟨⟨a, b⟩, hp, rfl⟩ := List.mem_map.1 hx
      have hp' : a ∈ S ∧ b ∈ St := by simpa [List.product] using hp
      exact H.mul_mem (hS _ hp'.1) (hSt _ hp'.2)

theorem O3_le_A : ∀ x ∈ O3 (), x ∈ A := by
  refine closeFuel_le A o3Steps ?_ 6 [1] (by simp [A.one_mem])
  have hg : ∀ s ∈ o3Gens, s ∈ A := by
    intro s hs
    simp only [o3Gens, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact sigma1_memA
    · exact o3b_memA
    · exact o3c_memA
  intro s hs
  rw [o3Steps, List.mem_append] at hs
  rcases hs with hs | hs
  · exact hg s hs
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact A.inv_mem (hg t ht)

theorem center_O3' {x : P45} :
    (x ∈ O3 () ∧ ∀ y ∈ O3 (), x * y = y * x) ↔ x = 1 ∨ x = sigma1 ∨ x = sigma1 * sigma1 := by
  constructor
  · rintro ⟨hx, hc⟩
    have hb := congrArg cOf (hc o3b o3b_mem_O3)
    have hcc := congrArg cOf (hc o3c o3c_mem_O3)
    rw [cOf_mul, cOf_mul] at hb hcc
    rw [mem_O3] at hx
    have h := List.all_eq_true.1 o3c_more.1 _ hx
    rw [eq22C_eq, eq22C_eq, decide_eq_true hb, decide_eq_true hcc] at h
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact Or.inl (cOf_inj ((eq_of_beq h).trans cOf_one.symm))
    · exact Or.inr (Or.inl (cOf_inj (eq_of_beq h)))
    · exact Or.inr (Or.inr (cOf_inj ((eq_of_beq h).trans (cOf_mul _ _).symm)))
  · rintro (rfl | rfl | rfl)
    · exact ⟨o3_one, fun y _ => by rw [one_mul, mul_one]⟩
    · exact ⟨s1_mem_O3, fun y hy => (o3_comm_s1 hy).symm⟩
    · refine ⟨o3_mul s1_mem_O3 s1_mem_O3, fun y hy => ?_⟩
      rw [mul_assoc, ← o3_comm_s1 hy, ← mul_assoc, ← o3_comm_s1 hy, mul_assoc]

@[expose] def zg (k : ℕ) : P45 := ((zW.getD k []).map gA').prod

theorem prep_zg : ∀ k < 6, PRep 45 6 (CZ.G k) (zg k) ∧ zg k ∈ A :=
  fun _ hk => prep_word Parrott946.binds.2.2.2.2.2.2.2.2.2.2.2.2 hk

theorem prep_s1 : PRep 45 6 (K1.T K1.r0) sigma1 := by
  rw [← Parrott946.binds.2.2.2.2.2.2.2.2.2.1]
  exact prep_cOf _

theorem centS1_eq :
    Subgroup.closure (zg '' {k | k < 6}) = A ⊓ centralizer ({sigma1} : Set P45) := by
  obtain ⟨hcard, -⟩ := group_A (fun k hk => (prep_zg k hk).1) CZ.cl CZ.tr (by norm_num)
    Parrott946.ids CZ.k
  have hle : Subgroup.closure (zg '' {k | k < 6}) ≤ A ⊓ centralizer ({sigma1} : Set P45) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    refine mem_inf.2 ⟨(prep_zg k hk).2, mem_centralizer_singleton_iff.2 ?_⟩
    exact comm_of_eq22 (prep_zg k hk).1 prep_s1 (allN_spec Parrott946.cent k hk)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_cent_s1, hcard])

theorem O3_normal' {c : P45}
    (hc : c ∈ A ⊓ centralizer ({sigma1} : Set P45)) {x : P45} (hx : x ∈ O3 ()) :
    c * x * c⁻¹ ∈ O3 () := by
  rw [← centS1_eq] at hc
  refine conj_closed_A (O := {x | x ∈ O3 ()}) ?_ c hc x hx
  rintro _ ⟨k, hk, rfl⟩ y hy
  have hy' : cOf y ∈ O3C := mem_O3.1 hy
  obtain ⟨b, hb, h⟩ := List.any_eq_true.1
    (List.all_eq_true.1 (allN_spec o3c_more.2.1 k hk) _ hy')
  have e := mul_eq_of_eq22 (prep_zg k hk).1 (prep_cOf y) (prep_ev b) (prep_zg k hk).1 h
  change zg k * y * (zg k)⁻¹ ∈ O3 ()
  rw [e, mul_inv_cancel_right]
  exact ev_mem_O3 hb

theorem cls_s12i :
    ∀ i < 480, ∀ v, PRep 45 6 (K12i.T i) v → ∃ g ∈ A, v = g * (sigma1 * sigma2⁻¹) * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, h0, h1, h2, -, -, bt, -⟩ := Parrott946.binds
  exact (class_A K12i.h (prep_gens h0 h1 h2) K12i.cl K12i.tr0 (by decide)
    (by rw [← bt]; exact prep_cOf _) K12i.k).2

theorem card_cent_one :
    Nat.card ↥(A ⊓ centralizer ({1} : Set P45)) = 51840 := by
  have e : centralizer ({1} : Set P45) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff]
    exact Subgroup.one_mem _
  rw [e, inf_top_eq, card_A]

theorem card_cent_s1sq (h : v * sigma1 * v⁻¹ = sigma1 * sigma1) :
    Nat.card ↥(A ⊓ centralizer ({sigma1 * sigma1} : Set P45)) = 648 := by
  rw [← h, card_cent_conj v_memA]
  exact card_cent_s1

theorem class_O3' (hv : v * sigma1 * v⁻¹ = sigma1 * sigma1)
    {x : P45} : (x ∈ O3 () ∧ ∃ g ∈ A, x = g * (sigma1 * sigma2⁻¹) * g⁻¹) ↔
      (x ∈ O3 () ∧ ¬ (x = 1 ∨ x = sigma1 ∨ x = sigma1 * sigma1)) := by
  constructor
  · rintro ⟨hx, g, hg, rfl⟩
    refine ⟨hx, fun h => ?_⟩
    have hc := card_cent_conj (t := sigma1 * sigma2⁻¹) hg
    rw [card_cent_s12i] at hc
    rcases h with h | h | h
    · rw [h, card_cent_one] at hc
      omega
    · rw [h, card_cent_s1] at hc
      omega
    · rw [h, card_cent_s1sq hv] at hc
      omega
  · rintro ⟨hx, hn⟩
    refine ⟨hx, ?_⟩
    have hx' := mem_O3.1 hx
    have h := List.all_eq_true.1 o3c_more.2.2 _ hx'
    simp only [Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact absurd (Or.inl (cOf_inj ((eq_of_beq h).trans cOf_one.symm))) hn
    · exact absurd (Or.inr (Or.inl (cOf_inj (eq_of_beq h)))) hn
    · exact absurd (Or.inr (Or.inr (cOf_inj ((eq_of_beq h).trans (cOf_mul _ _).symm)))) hn
    · obtain ⟨j, hj, e⟩ := memK_spec h
      refine cls_s12i j hj x ?_
      rw [e]
      exact prep_cOf x

end CertificateChecks.Parrott946

end
