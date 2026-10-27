
module

public import Certificates.Kernel.Parrott946.Glue17d

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

theorem t_comm_T0g : T0g ≤ centralizer ({t} : Set P45) := by
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_centralizer_singleton_iff.2
    (comm_of_cmm prep_t (prep_g0 k hk) (allN_spec c17_zc.2 k hk)).symm

theorem centre_T0g {z : P45} (hz : z ∈ T0g) (hc : ∀ k < 6, z * g0 k = g0 k * z) :
    z = 1 ∨ z = t := by
  obtain ⟨c, hcT, hall, -⟩ := t0_enum
  obtain ⟨i, hi, rfl⟩ := hall z hz
  have h := allN_spec c17_zc.1 i hi
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · have : allN 6 (fun k => eq22 45 6 (mask 6) (T0Z.T i) (T0Z.G k) (T0Z.G k) (T0Z.T i)) = true :=
      allN_iff.2 fun k hk => eq22_of_mul17 (hcT i hi).1 (prep_g0 k hk) (prep_g0 k hk) (hcT i hi).1
        (hc k hk)
    rw [this] at h
    exact absurd h (by decide)
  · exact Or.inl ((isIdK_iff (hcT i hi).1).1 h)
  · exact Or.inr (eq_of_eqP h (hcT i hi).1 prep_t)

theorem T0Z_lt : allN 128 (fun j => Nat.blt (T0Z.T j) (2 ^ 270)) = true := by decide +kernel

set_option exponentiation.threshold 300 in
theorem not_mem_T0g {P Q : ℕ} {x : P45} (hx : PRep 45 6 (pc P Q) x)
    (h : memK 45 6 ps T0Z.N T0Z.T T0Z.S (pc P Q) = false) : x ∉ T0g := by
  intro hxT
  obtain ⟨c, hcT, hall, -⟩ := t0_enum
  obtain ⟨i, hi, rfl⟩ := hall x hxT
  have e : T0Z.T i = pc P Q :=
    prep_canon_eq (hcT i hi).1 hx (Nat.blt_eq.mp (allN_spec T0Z_lt i hi)) (pcomp_lt (by norm_num))
  rw [← e, memK_complete T0Z.k (by decide) hi] at h
  exact absurd h (by decide)

@[expose] noncomputable def rr (i : ℕ) : P45 := wv17 (12 + i)

@[expose] noncomputable def ri (i : ℕ) : P45 := wv17 (21 + i)

theorem prep_rr {i : ℕ} (hi : i < 9) : PRep 45 6 (rE i) (rr i) ∧ rr i ∈ A :=
  prep_wE (k := 12 + i) (by omega)

theorem prep_ri {i : ℕ} (hi : i < 9) : PRep 45 6 (rI i) (ri i) :=
  (prep_wE (k := 21 + i) (by omega)).1

theorem cos_facts {i : ℕ} (hi : i < 9) : ri i = (rr i)⁻¹ ∧ rr i * t = t * rr i := by
  have h := allN_spec c17_cos.2.1 i hi
  rw [bAnd_eq, Bool.and_eq_true] at h
  have e := eq_of_eqP h.1 (prep_pc (prep_rr hi).1 (prep_ri hi)) prep_pid
  exact ⟨eq_inv_of_mul_eq_one_right e, comm_of_cmm (prep_rr hi).1 prep_t h.2⟩

theorem rr_zero : rr 0 = 1 := eq_of_eqP c17_cos.1 (prep_rr (by norm_num)).1 prep_pid

theorem cos_sep {i j : ℕ} (hi : i < 9) (hj : j < 9) (hij : i < j) : rr j * (rr i)⁻¹ ∉ T0g := by
  have h := allN_spec (allN_spec c17_cos.2.2.1 i hi) j hj
  rw [Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h
  rcases h with h | h
  · rw [Nat.blt_eq.mpr hij] at h
    exact absurd h (by decide)
  · have hp := prep_pc (prep_rr hj).1 (prep_ri hi)
    rw [(cos_facts hi).1] at hp
    exact not_mem_T0g hp h

theorem T0g_le_cent :
    T0g ≤ A ⊓ centralizer ({t} : Set P45) := le_inf T0g_le_A t_comm_T0g

theorem cent_t_cosets {c : P45} (hc : c ∈ A)
    (hct : c * t = t * c) : ∃ i < 9, c * (rr i)⁻¹ ∈ T0g := by
  have hrC : ∀ i : Fin 9, rr i ∈ A ⊓ centralizer ({t} : Set P45) := fun i =>
    mem_inf.2 ⟨(prep_rr i.2).2, mem_centralizer_singleton_iff.2 (cos_facts i.2).2⟩
  let f : Fin 9 × T0g → ↥(A ⊓ centralizer ({t} : Set P45)) := fun p =>
    ⟨p.2.1 * rr p.1, (A ⊓ centralizer ({t} : Set P45)).mul_mem (T0g_le_cent p.2.2) (hrC p.1)⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, s⟩ ⟨j, s'⟩ e
    have e' : s.1 * rr i = s'.1 * rr j := congrArg Subtype.val e
    have key : ∀ {a b : Fin 9} {x y : P45}, x ∈ T0g → y ∈ T0g → (a : ℕ) < b →
        x * rr a = y * rr b → False := by
      intro a b x y hx hy hab e2
      apply cos_sep a.2 b.2 hab
      have : rr b * (rr a)⁻¹ = y⁻¹ * x := by
        calc rr b * (rr a)⁻¹ = y⁻¹ * (y * rr b) * (rr a)⁻¹ := by group
          _ = y⁻¹ * (x * rr a) * (rr a)⁻¹ := by rw [e2]
          _ = y⁻¹ * x := by group
      rw [this]
      exact T0g.mul_mem (T0g.inv_mem hy) hx
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact (key s.2 s'.2 h e').elim
    · have hij : i = j := Fin.ext h
      subst hij
      have : s.1 = s'.1 := mul_right_cancel e'
      rw [Subtype.ext this]
    · exact (key s'.2 s.2 h e'.symm).elim
  have hcard : Nat.card ↥(A ⊓ centralizer ({t} : Set P45)) ≤ Nat.card (Fin 9 × T0g) := by
    rw [Nat.card_prod, Nat.card_fin, card_T0g, card_cent_t Alg.t_sq Alg.t_ne_one]
  obtain ⟨⟨i, s⟩, e⟩ := (hinj.bijective_of_nat_card_le hcard).2
    ⟨c, mem_inf.2 ⟨hc, mem_centralizer_singleton_iff.2 hct⟩⟩
  refine ⟨i, i.2, ?_⟩
  have e' : s.1 * rr i = c := congrArg Subtype.val e
  rw [← e', mul_inv_cancel_right]
  exact s.2

theorem norm_T0g {c : P45} (hc : c ∈ A)
    (hN : ∀ k < 6, c * g0 k * c⁻¹ ∈ T0g) : c ∈ T0g := by
  have hmap : T0g.map (MulAut.conj c).toMonoidHom ≤ T0g := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact hN k hk
  have hconj : ∀ y ∈ T0g, c * y * c⁻¹ ∈ T0g := fun y hy => hmap ⟨y, hy, rfl⟩
  have hmapeq : T0g.map (MulAut.conj c).toMonoidHom = T0g :=
    Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj c))])
  have hz : c * t * c⁻¹ = t := by
    have hzT : c * t * c⁻¹ ∈ T0g := hconj t t_mem_T0g
    have hzc : ∀ k < 6, c * t * c⁻¹ * g0 k = g0 k * (c * t * c⁻¹) := by
      intro k hk
      have hk' : g0 k ∈ T0g.map (MulAut.conj c).toMonoidHom := by
        rw [hmapeq]
        exact g0_mem hk
      obtain ⟨y, hy, e⟩ := hk'
      have e' : c * y * c⁻¹ = g0 k := e
      have hty := mem_centralizer_singleton_iff.1 (t_comm_T0g hy)
      rw [← e']
      calc c * t * c⁻¹ * (c * y * c⁻¹) = c * (t * y) * c⁻¹ := by group
        _ = c * (y * t) * c⁻¹ := by rw [hty]
        _ = c * y * c⁻¹ * (c * t * c⁻¹) := by group
    rcases centre_T0g hzT hzc with h | h
    · exfalso
      apply Alg.t_ne_one
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hct : c * t = t * c := by
    calc c * t = c * t * c⁻¹ * c := by group
      _ = t * c := by rw [hz]
  obtain ⟨i, hi, hs⟩ := cent_t_cosets hc hct
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    rw [rr_zero, inv_one, mul_one] at hs
    exact hs
  · exfalso
    obtain ⟨i', rfl⟩ : ∃ i', i = Nat.succ i' := ⟨i - 1, by omega⟩
    have h := allN_spec c17_cos.2.2.2 i' (by omega)
    rw [Bool.not_eq_true', Bool.eq_false_iff] at h
    apply h
    refine allN_iff.2 fun k hk => ?_
    have hr := prep_rr hi
    have hp := prep_pc hr.1 (prep_pc (prep_g0 k hk) (prep_ri hi))
    rw [(cos_facts hi).1] at hp
    by_contra hm
    rw [Bool.not_eq_true] at hm
    apply not_mem_T0g hp hm
    have e : rr (Nat.succ i') * (g0 k * (rr (Nat.succ i'))⁻¹) =
        (c * (rr (Nat.succ i'))⁻¹)⁻¹ * (c * g0 k * c⁻¹) * (c * (rr (Nat.succ i'))⁻¹) := by group
    rw [e]
    exact T0g.mul_mem (T0g.mul_mem (T0g.inv_mem hs) (hconj (g0 k) (g0_mem hk))) hs

theorem t0_normalizer : t0NormalizerCheck () = true := by
  unfold t0NormalizerCheck
  rw [tabList_eq]
  refine List.all_eq_true.2 fun c hc => ?_
  have hcA : c ∈ A := (mem_elemsT QA45 QA45_ok c).1 hc
  rw [Bool.or_eq_true]
  by_cases hn : ∀ x ∈ T0gens, c * x * c⁻¹ ∈ T0list ()
  · refine Or.inr (decide_eq_true ((t0_set c).2 (norm_T0g hcA fun k hk => ?_)))
    refine (t0_set _).1 (hn _ ?_)
    interval_cases k <;> simp [g0, T0gens]
  · refine Or.inl ?_
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro h
    exact hn fun x hx => of_decide_eq_true (List.all_eq_true.1 h x hx)

end CertificateChecks.Parrott946

end
