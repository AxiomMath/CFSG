
module

public import Certificates.Kernel.HN1408.CzInvFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT

theorem conj_into_of_odd_index {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (hK : ¬ 2 ∣ K.index) (x : G) (hx : x * x = 1) : ∃ g : G, g * x * g⁻¹ ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T0⟩ : Nonempty (Sylow 2 K) := inferInstance
  set T : Subgroup G := (T0 : Subgroup K).map K.subtype with hTdef
  have hTp : IsPGroup 2 T := T0.isPGroup'.map K.subtype
  have hTidx : ¬ 2 ∣ T.index := by
    have h1 := Subgroup.card_mul_index T
    have h2 := Subgroup.card_mul_index (T0 : Subgroup K)
    have h3 := Subgroup.card_mul_index K
    have hc : Nat.card T = Nat.card (T0 : Subgroup K) :=
      Subgroup.card_map_of_injective K.subtype_injective
    have e : Nat.card T * T.index = Nat.card T * ((T0 : Subgroup K).index * K.index) := by
      rw [h1, hc, ← mul_assoc, h2, h3]
    rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos e]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · exact T0.not_dvd_index h
    · exact hK h
  let TS : Sylow 2 G := hTp.toSylow hTidx
  have hXp : IsPGroup 2 (Subgroup.zpowers x) := by
    have hx2 : x ^ 2 = 1 := by rw [sq, hx]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (by simpa using hx2) : orderOf x ∣ 2 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hXp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q TS
  refine ⟨g, ?_⟩
  have hmem : g * x * g⁻¹ ∈ (TS : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have hm := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup G)
      (hQ (Subgroup.mem_zpowers x))
    rwa [MulAut.smul_def, MulAut.conj_apply] at hm
  have e : (TS : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  rw [e, hTdef] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  rw [← hy]
  exact y.2

theorem conj_into_cz (hP : Nat.card ↥P1408 = 177408000) {x : Equiv.Perm (Fin 1408)}
    (hxP : x ∈ P1408) (hx : x * x = 1) :
    ∃ c ∈ P1408, c * x * c⁻¹ ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  set K : Subgroup ↥P1408 :=
    (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))).subgroupOf P1408 with hKdef
  have hKc : Nat.card K = 30720 := by
    rw [hKdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      ← (czT_eq hP).1]
    exact (czT_eq hP).2
  have hKi : K.index = 5775 := by
    have h := Subgroup.card_mul_index K
    rw [hKc, hP] at h
    omega
  obtain ⟨g, hg⟩ := conj_into_of_odd_index K (by rw [hKi]; decide) ⟨x, hxP⟩ (Subtype.ext hx)
  refine ⟨g, g.2, ?_⟩
  rw [hKdef, Subgroup.mem_subgroupOf] at hg
  exact hg

@[expose] noncomputable def namedA (t : Nat) : Equiv.Perm (Fin 1408) := if t = 0 then elemA else namedE t

theorem repC_namedA {t : Nat} (h5 : t < 5) : RepC (namedP t) (namedA t) := by
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · have e : namedP 0 = WK wordA := rfl
    have e' : namedA 0 = elemA := by simp [namedA]
    rw [e, e']
    exact repC_word (by decide)
  · have e' : namedA t = namedE t := by simp [namedA, Nat.pos_iff_ne_zero.1 h0]
    rw [e']
    exact repC_named h0 h5

theorem namedA_mem {t : Nat} (h5 : t < 5) : namedA t ∈ P1408 := by
  interval_cases t <;> simp only [namedA, namedE] <;> norm_num <;>
    first
    | exact elemW_mem _
    | exact mul_mem (elemW_mem _) (elemW_mem _)

theorem named_eq (hP : Nat.card ↥P1408 = 177408000) {c : Nat} (hc : c < 5) :
    fd (R c) 0 < 1280 ∧ fd (R c) 1 < 24 ∧ repE c = namedA c := by
  have h := named_ok
  unfold namedK at h
  rw [strictB_app] at h
  have h' := allN_spec h c hc
  simp only [strictB_app] at h'
  obtain ⟨hq, h'⟩ := mkA h'
  obtain ⟨hq', h'⟩ := mkA h'
  obtain ⟨hcomm, hb⟩ := mkA h'
  have hq1 := Nat.blt_eq.mp hq
  have hq2 := Nat.blt_eq.mp hq'
  have hX := repC_namedA hc
  have hmem := mem_cent_of hX (namedA_mem hc) hcomm
  refine ⟨hq1, hq2, base_eq hP (mem_cz hP hq1 hq2) hmem (fun y hy => ev_eq hq1 hq2 hy)
    (repC_pt hX (by norm_num)).symm (repC_pt hX (by norm_num)).symm hb⟩

theorem involution_cover (hP : Nat.card ↥P1408 = 177408000) {x : Equiv.Perm (Fin 1408)}
    (hxP : x ∈ P1408) (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ t < 5, ∃ c ∈ P1408, x = c * namedA t * c⁻¹ := by
  obtain ⟨c, hcP, hcz⟩ := conj_into_cz hP hxP hx
  have h2 : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have h1 : c * x * c⁻¹ ≠ 1 := fun e => hx1 (by
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [e]; group)
  obtain ⟨k, hk, -, -, h, hh, e⟩ := inv_conj hP hcz h2 h1
  have hhP : h ∈ P1408 := (Subgroup.mem_inf.1 hh).1
  have e' : x = (c⁻¹ * h) * repE k * (c⁻¹ * h)⁻¹ := by
    calc x = c⁻¹ * (c * x * c⁻¹ * h) * h⁻¹ * c := by group
      _ = c⁻¹ * (h * repE k) * h⁻¹ * c := by rw [e]
      _ = _ := by group
  have hch : c⁻¹ * h ∈ P1408 := mul_mem (inv_mem hcP) hhP
  by_cases hk5 : k < 5
  · refine ⟨k, hk5, c⁻¹ * h, hch, ?_⟩
    rw [e', (named_eq hP hk5).2.2]
  · obtain ⟨t, ht0, ht5, -, -, g, hgP, hg⟩ := rep_wit (c := k) (by omega) hk
    have hrep : repE k = g * namedE t * g⁻¹ := hg
    have hA : namedA t = namedE t := by simp [namedA, Nat.pos_iff_ne_zero.1 ht0]
    refine ⟨t, ht5, (c⁻¹ * h) * g, mul_mem hch hgP, ?_⟩
    rw [e', hrep, hA]
    group

end CFSG.KD.HN1408.CzInv

end
