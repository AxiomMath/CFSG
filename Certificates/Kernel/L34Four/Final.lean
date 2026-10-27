module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Kernel.L34Four.Checks
public import CFSG.Certificates.Kernel.L34FourSound

public section

namespace CFSG.KD.L34Four

open Subgroup CFSG.ComponentClassification.PSL3Four CFSG.KC.Enum CFSG.KS
open CFSG.KD.J3Four (PRep getN)

@[expose] def gσ (k : ℕ) : Equiv.Perm (Fin 42) := [g₁, g₂, g₃, g₄, g₅, g₆].getD k 1

@[expose] def gT (k : ℕ) : Array ℕ :=
  [CFSG.PSL3Four.Native.g₁T, CFSG.PSL3Four.Native.g₂T, CFSG.PSL3Four.Native.g₃T,
    CFSG.PSL3Four.Native.g₄T, CFSG.PSL3Four.Native.g₅T, CFSG.PSL3Four.Native.g₆T].getD k #[]

theorem gens_ok :
    (allN 6 fun k => allN 42 fun q => Nat.beq (pg 13 (mask 13) (getN G6 k) q) (gT k)[q]!) =
      true := by
  decide +kernel

theorem G6_length : G6.length = 6 := by decide +kernel

theorem tabRep_gT : ∀ k < 6, TabRep (gT k) (gσ k) := by
  intro k hk
  interval_cases k
  · exact tabRep_g₁
  · exact tabRep_g₂
  · exact tabRep_g₃
  · exact tabRep_g₄
  · exact tabRep_g₅
  · exact tabRep_g₆

theorem prep_G6 : ∀ k < G6.length, PRep 42 (getN G6 k) (gσ k) := by
  intro k hk q hq
  rw [G6_length] at hk
  have h := CFSG.KS.allN_spec (CFSG.KS.allN_spec gens_ok k hk) q hq
  rw [Nat.beq_eq] at h
  rw [h]
  exact (tabRep_gT k hk).apply ⟨q, hq⟩

theorem gσ_mem : ∀ k < G6.length, gσ k ∈ R := by
  intro k hk
  rw [G6_length] at hk
  interval_cases k <;> exact subset_closure (by simp [gσ])

theorem card_carrier_mul {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer {g}) = Nat.card G := by
  rw [← ConjAct.orbit_eq_carrier_conjClasses, Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

theorem card_cent_R (x : R) : Nat.card ↥(Subgroup.centralizer ({x} : Set R)) =
    Nat.card ↥(R ⊓ centralizer ({(x : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42)))) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1.1, mem_inf.2 ⟨y.1.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩⟩
      invFun := fun y => ⟨⟨y.1, (mem_inf.1 y.2).1⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2))⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }


theorem card_cent_eq {x : R} {k : ℕ} (hk : Nat.card (ConjClasses.mk x).carrier = k) :
    k * Nat.card ↥(R ⊓ centralizer ({(x : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42)))) =
      241920 := by
  rw [← card_cent_R, ← hk, card_carrier_mul]
  exact card_R

theorem inv_of_orderOf {x : R} (hx : orderOf x = 2) :
    (x : Equiv.Perm (Fin 42)) * x = 1 ∧ (x : Equiv.Perm (Fin 42)) ≠ 1 := by
  refine ⟨?_, fun h => ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx, pow_two] at this
    exact congrArg Subtype.val this
  · have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)

theorem dvd_of_card {K : Subgroup (Equiv.Perm (Fin 42))} {k : ℕ} (hK : Nat.card K = k)
    (hk : k ∣ 2 ^ 30 * 3 ^ 30) (w : Equiv.Perm (Fin 42)) :
    Nat.card ↥(K ⊓ centralizer ({w} : Set (Equiv.Perm (Fin 42)))) ∣ 2 ^ 30 * 3 ^ 30 :=
  (hK ▸ card_dvd_of_le inf_le_left).trans hk

theorem l34Four_facts :
    (∀ t ∈ R, t * t = 1 → t ≠ 1 → ∃ r ∈ [r₁, r₂, r₃, r₄], ∃ g ∈ R, t = g * r * g⁻¹) ∧
      ∀ r ∈ [r₁, r₂, r₃, r₄], ∀ w ∈ R ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 42))),
        w * w = 1 → w ≠ 1 → w ≠ r →
          Nat.card ↥((R ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 42)))) ⊓
            centralizer ({w} : Set (Equiv.Perm (Fin 42)))) ∣ 2 ^ 30 * 3 ^ 30 := by
  obtain ⟨-, -, -, -, -, hinv, -, h1, h2, h3, h4, -⟩ := involution_enumeration
  refine ⟨fun t ht htt ht1 => ?_, fun r hr => ?_⟩
  · have hx : orderOf (⟨t, ht⟩ : R) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (Subtype.ext ?_) (fun h => ht1 (congrArg Subtype.val h))
      change t ^ 2 = 1
      rw [pow_two, htt]
    rcases (hinv ⟨t, ht⟩).1 hx with h | h | h | h <;>
      obtain ⟨c, hc, he⟩ := eq_conj_of_isConj h
    · exact ⟨r₁, by simp, c, hc, he⟩
    · exact ⟨r₂, by simp, c, hc, he⟩
    · exact ⟨r₃, by simp, c, hc, he⟩
    · exact ⟨r₄, by simp, c, hc, he⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · intro w _ _ _ _
      have e : 315 * Nat.card ↥(R ⊓ centralizer ({r₁} : Set (Equiv.Perm (Fin 42)))) = 241920 :=
        card_cent_eq (x := r₁R) h1
      exact dvd_of_card (k := 768) (by omega) (by norm_num) w
    · have e : 360 * Nat.card ↥(R ⊓ centralizer ({gσ 4} : Set (Equiv.Perm (Fin 42)))) =
          241920 := card_cent_eq (x := r₂R) h2
      have hrr : gσ 4 * gσ 4 = 1 ∧ gσ 4 ≠ 1 := inv_of_orderOf orderOf_r₂R
      have h4r : gσ 4 = r₂ := rfl
      rw [← h4r]
      exact four_of_rowL R prep_G6 gσ_mem (by simp) row2_ok Nat.prime_seven (by norm_num)
        (by norm_num) (a := 5) (b := 1) (by norm_num) (by norm_num) (by omega) (by omega)
        hrr.1 hrr.2
    · have e : 1008 * Nat.card ↥(R ⊓ centralizer ({gσ 5} : Set (Equiv.Perm (Fin 42)))) =
          241920 := card_cent_eq (x := r₃R) h3
      have hrr : gσ 5 * gσ 5 = 1 ∧ gσ 5 ≠ 1 := inv_of_orderOf orderOf_r₃R
      have h5r : gσ 5 = r₃ := rfl
      rw [← h5r]
      exact four_of_rowL R prep_G6 gσ_mem (by simp) row3_ok Nat.prime_five (by norm_num)
        (by norm_num) (a := 4) (b := 1) (by norm_num) (by norm_num) (by omega) (by omega)
        hrr.1 hrr.2
    · intro w _ _ _ _
      have e : 280 * Nat.card ↥(R ⊓ centralizer ({r₄} : Set (Equiv.Perm (Fin 42)))) = 241920 :=
        card_cent_eq (x := r₄R) h4
      exact dvd_of_card (k := 864) (by omega) (by norm_num) w

end CFSG.KD.L34Four

end
