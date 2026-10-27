module

public import Certificates.Kernel.HN1408.Cent3TT
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Cent3Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cent3

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem row_inv {k : Nat} (hk : k < 1440) (h0 : R k ≠ 0) : invK k = true := by
  have h := allN_spec ch441603_rows k hk
  unfold rowK at h
  have e0 : Nat.beq (R k) 0 = false := Bool.eq_false_iff.2 fun h' => h0 (Nat.eq_of_beq_eq_true h')
  simp only [strictB_app] at h
  rw [e0] at h
  exact (mkA h).1

theorem ttK_zero : ttK RT 0 = 0 := rfl

theorem hC_of (hpf : PrimeFacts 3 [fix3]) : Nat.card cC = 1440 := by
  obtain ⟨hcard, hcl⟩ := hpf.1 fix3 (by simp)
  change Nat.card ↥(closure (elemW '' {w | w ∈ fix3.cent})) = 1440
  rw [hcl]
  exact hcard

theorem mem_cent_iff (hpf : PrimeFacts 3 [fix3]) (y : ↥P1408) :
    y ∈ centralizer ({repP fix3} : Set ↥P1408) ↔ (y : Equiv.Perm (Fin 1408)) ∈ cC := by
  obtain ⟨-, hcl⟩ := hpf.1 fix3 (by simp)
  change _ ↔ (y : Equiv.Perm (Fin 1408)) ∈ closure (elemW '' {w | w ∈ fix3.cent})
  rw [hcl, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨y.2, by simpa [repP] using congrArg Subtype.val h⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext (by simpa [repP] using h)

variable (hpf : PrimeFacts 3 [fix3]) (hnc : ∀ i j : Fin 5, i ≠ j → ¬ IsConj (vH i) (vH j))
include hpf hnc

theorem tt_mem {k : Nat} (hk : k < 1440) (h1 : ttK RT (R k) = 1) :
    elH hk ∈ centralizer ({repP fix3} : Set ↥P1408) ∧ elH hk ^ 2 = 1 ∧ elH hk ≠ 1 ∧
      tTH pA pZ pZ₁ (elH hk) := by
  have hC := hC_of hpf
  have h0 : R k ≠ 0 := fun h => by rw [h, ttK_zero] at h1; exact absurd h1 (by norm_num)
  obtain ⟨hsq, hne⟩ := (invK_iff hC hk).1 (row_inv hk h0)
  have hy2 : elH hk ^ 2 = 1 :=
    Subtype.ext (by rw [pow_two, Subgroup.coe_mul, elH_val, hsq]; rfl)
  have hy1 : elH hk ≠ 1 := fun e => hne (by rw [← elH_val hk, e]; rfl)
  have hmem : ((elH hk : ↥P1408) : Equiv.Perm (Fin 1408)) ∈ cC := by
    rw [elH_val]
    exact el_mem hk
  obtain ⟨k', hk', hyk, h0', ht, hconj⟩ := inv_conj hC hmem hy2 hy1
  rw [elH_val] at hyk
  obtain rfl : k = k' := el_inj hk hk' hyk
  exact ⟨(mem_cent_iff hpf _).2 hmem, hy2, hy1, (tTH_iff hC hnc h0' ht hconj).2 h1⟩

theorem tt_el {y : ↥P1408} (hyc : y ∈ centralizer ({repP fix3} : Set ↥P1408)) (hy2 : y ^ 2 = 1)
    (hy1 : y ≠ 1) (ht : tTH pA pZ pZ₁ y) :
    ∃ k < 1440, ttK RT (R k) = 1 ∧ (y : Equiv.Perm (Fin 1408)) = el k := by
  have hC := hC_of hpf
  obtain ⟨k, hk, hyk, h0, ht', hconj⟩ := inv_conj hC ((mem_cent_iff hpf y).1 hyc) hy2 hy1
  exact ⟨k, hk, (tTH_iff hC hnc h0 ht' hconj).1 ht, hyk⟩

theorem card_tT : CardTTAt pA pZ pZ₁ (repP fix3) := by
  classical
  unfold CardTTAt
  let K : Finset Nat := (Finset.range 1440).filter fun k => ttK RT (R k) = 1
  have himg : Subtype.val '' {y : ↥P1408 | y ∈ centralizer ({repP fix3} : Set ↥P1408) ∧
      y ^ 2 = 1 ∧ y ≠ 1 ∧ tTH pA pZ pZ₁ y} = el '' (↑K : Set Nat) := by
    ext g
    constructor
    · rintro ⟨y, ⟨hyc, hy2, hy1, ht⟩, rfl⟩
      obtain ⟨k, hk, h1, hyk⟩ := tt_el hpf hnc hyc hy2 hy1 ht
      exact ⟨k, by simp [K, hk, h1], hyk.symm⟩
    · rintro ⟨k, hkK, rfl⟩
      have hkK' : k < 1440 ∧ ttK RT (R k) = 1 := by simpa [K] using hkK
      exact ⟨elH hkK'.1, tt_mem hpf hnc hkK'.1 hkK'.2, elH_val hkK'.1⟩
  have hinj : Set.InjOn el (↑K : Set Nat) := fun k hk k' hk' e =>
    el_inj (by simp [K] at hk; exact hk.1) (by simp [K] at hk'; exact hk'.1) e
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
    hinj.ncard_image, Set.ncard_coe_finset, ← cntN_eq]
  exact Nat.eq_of_beq_eq_true ch441603_cnt

end CFSG.KD.HN1408.Cent3

end
