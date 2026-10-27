
module

public import Certificates.Kernel.Parrott946.Glue17n

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup
  CFSG.Sporadic.SmallOddCore CFSG.KC.SylowReps

local notation "P45" => Equiv.Perm (Fin 45)

abbrev CB : Subgroup P45 := A ⊓ centralizer ({b5} : Set P45)

theorem mem_CB {x : P45} : x ∈ CB ↔ x ∈ A ∧ x * b5 = b5 * x := by
  rw [mem_inf, mem_centralizer_singleton_iff]

theorem card_CB_dvd : Nat.card CB ∣ 51840 := by
  rw [← card_A]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem five_dvd_CB : 5 ∣ Nat.card CB := by
  rw [← orderOf_b5]
  exact Subgroup.orderOf_dvd_natCard _ (mem_CB.2 ⟨b5_memA, rfl⟩)

theorem three_ndvd_CB : ¬ 3 ∣ Nat.card CB := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := CB) 3 h3
  have hx' : orderOf (x : P45) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hc := mem_CB.1 x.2
  have h3' : (x : P45) * x * x = 1 := by
    have h := pow_orderOf_eq_one (x : P45)
    rwa [hx', pow_succ, sq] at h
  have h1 : (x : P45) ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hx'
    omega
  exact no_ord3_comm_b5 hc.1 h3' h1 hc.2

theorem card_CB_form : ∃ a ≤ 7, Nat.card CB = 5 * 2 ^ a := by
  obtain ⟨d, hd⟩ := five_dvd_CB
  have h640 : Nat.card CB ∣ 640 := by
    have hc : Nat.Coprime (3 ^ 4) (Nat.card CB) :=
      Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 three_ndvd_CB)
    have e : (51840 : ℕ) = 3 ^ 4 * 640 := by norm_num
    have h := card_CB_dvd
    rw [e] at h
    exact (Nat.Coprime.dvd_of_dvd_mul_left hc.symm h)
  rw [hd] at h640
  have e640 : (640 : ℕ) = 5 * 2 ^ 7 := by norm_num
  rw [e640] at h640
  have hd128 : d ∣ 2 ^ 7 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5) h640
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd128
  exact ⟨a, ha, hd⟩

theorem uv_central {g : P45} (hg : g ∈ CB) :
    g * (u * v) * g⁻¹ = u * v := by
  have hg' := mem_CB.1 hg
  obtain ⟨hA, h2, h1⟩ := conj_inv hg'.1 uv_memA uv_inv.1 uv_inv.2
  refine inv_comm_b5 hA h2 h1 ?_
  have hb := b5_commutes
  have hgi : g⁻¹ * b5 = b5 * g⁻¹ := by
    calc g⁻¹ * b5 = g⁻¹ * (b5 * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * b5) * g⁻¹ := by rw [hg'.2]
      _ = b5 * g⁻¹ := by group
  calc g * (u * v) * g⁻¹ * b5 = g * (u * v) * (g⁻¹ * b5) := by group
    _ = g * (u * v) * (b5 * g⁻¹) := by rw [hgi]
    _ = g * ((u * v) * b5) * g⁻¹ := by group
    _ = g * (b5 * (u * v)) * g⁻¹ := by rw [hb]
    _ = g * b5 * (u * v) * g⁻¹ := by group
    _ = b5 * g * (u * v) * g⁻¹ := by rw [hg'.2]
    _ = b5 * (g * (u * v) * g⁻¹) := by group

abbrev CU : Subgroup P45 := A ⊓ centralizer ({u * v} : Set P45)

theorem not_a5 : Nat.card CB ≠ 160 := by
  intro h160
  have hdvd : 2 ^ 5 ∣ Nat.card CB := by rw [h160]; norm_num
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  let Q' : Subgroup P45 := Q.map CB.subtype
  have hQ' : Nat.card Q' = 2 ^ 5 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hQ]
  have hQB : ∀ x ∈ Q', x ∈ CB := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hQU : Q' ≤ CU := by
    intro x hx
    have hxB := hQB x hx
    refine mem_inf.2 ⟨(mem_CB.1 hxB).1, mem_centralizer_singleton_iff.2 ?_⟩
    calc x * (u * v) = x * (u * v) * x⁻¹ * x := by group
      _ = u * v * x := by rw [uv_central hxB]
  have htU : t ∈ CU := mem_inf.2 ⟨t_memA, mem_centralizer_singleton_iff.2 b5_facts.2.2.2.2⟩
  have ht32 : t ^ (2 ^ 5) = 1 := by
    have e : (2 : ℕ) ^ 5 = 2 * 16 := by norm_num
    rw [e, pow_mul, sq, Alg.t_sq, one_pow]
  have key := forall_of_sylow CU Q' Nat.prime_two hQU hQ' (k := 5) (m := 45)
    (by rw [card_cent_uv]; norm_num) (by decide) (fun x => x * x = 1 → x ≠ 1 → x = u * v)
    (by
      intro g hg x hx h hx2 hx1
      have hgc := mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2
      obtain ⟨-, h2, h1⟩ := conj_inv (mem_inf.1 hg).1 (mem_inf.1 hx).1 hx2 hx1
      have e := h h2 h1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (u * v) * g := by rw [e]
        _ = g⁻¹ * (g * (u * v)) := by rw [mul_assoc, ← hgc]
        _ = u * v := by group)
    (fun x hx hx2 hx1 => inv_comm_b5 (mem_CB.1 (hQB x hx)).1 hx2 hx1 (mem_CB.1 (hQB x hx)).2)
    t htU ht32 Alg.t_sq Alg.t_ne_one
  have hf := fixC_t
  rw [key, fixC_uv] at hf
  omega

end CertificateChecks.Parrott946

end
