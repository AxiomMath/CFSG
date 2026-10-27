
module

public import Certificates.Kernel.HN1408.M11Facts
public import Certificates.Kernel.HN1408.ClsBChk
public import Certificates.Kernel.HN1408.ClsZ1Chk0
public import Certificates.Kernel.HN1408.ClsZ1Chk1
public import Certificates.Kernel.HN1408.ClsZ1Chk2
public import Certificates.Kernel.HN1408.ClsZ1Srt
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.ClsR

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

#kc_forall_chunks b_rep_all (fun s => bRep s = true) 4 CFSG.KD.HN1408.ch26771cb.rep 1
#kc_forall_chunks b_srt_all (fun s => bSort s = true) 4 CFSG.KD.HN1408.ch26771cb.srt 1
#kc_forall_chunks z1_rep_all (fun s => z1Rep s = true) 42 CFSG.KD.HN1408.ch26771cz.rep 1
#kc_forall_chunks z1_srt_all (fun s => z1Sort s = true) 21 CFSG.KD.HN1408.ch26771cz.srt 1

theorem slice_index {i n len ns : Nat} (hi : i < n) (hn : n ≤ len * ns) :
    0 < len ∧ i / len < ns ∧ Nat.add (Nat.mul len (i / len)) (i % len) = i := by
  have hlen : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | h0
    · subst h0
      omega
    · exact h0
  refine ⟨hlen, Nat.div_lt_of_lt_mul (by omega), ?_⟩
  simp only [Nat.add_eq, Nat.mul_eq]
  exact Nat.div_add_mod i len

theorem repSl_all {R P : Nat → Nat} {n len ns : Nat} (hn : n ≤ len * ns)
    (h : ∀ s < ns, repSl R P n (Nat.mul len s) len = true) :
    ∀ i < n, 0 < i → repRK R P i = true := by
  intro i hi hpos
  obtain ⟨hlen, hs, e⟩ := slice_index hi hn
  have h' := allN_spec (h _ hs) (i % len) (Nat.mod_lt _ hlen)
  simp only [strictB_app] at h'
  rw [e, Nat.blt_eq.mpr hi] at h'
  have e0 : Nat.beq i 0 = false :=
    Bool.eq_false_iff.2 fun h'' => by have := Nat.eq_of_beq_eq_true h''; omega
  rw [e0] at h'
  exact h'

theorem sortSl_all {R S : Nat → Nat} {n cnt len ns : Nat} (hn : cnt ≤ len * ns)
    (h : ∀ s < ns, sortSl R S n cnt (Nat.mul len s) len = true) :
    ∀ m < cnt, sortAt R S n cnt m = true := by
  intro m hm
  obtain ⟨hlen, hs, e⟩ := slice_index hm hn
  have h' := allN_spec (h _ hs) (m % len) (Nat.mod_lt _ hlen)
  simp only [strictB_app] at h'
  rw [e, Nat.blt_eq.mpr hm] at h'
  exact h'

theorem repRK_parts {R P : Nat → Nat} {i : Nat} (h : repRK R P i = true) :
    ∃ p k j, p < i ∧ k < 11 ∧ j < 7 ∧
      (R i = pc (pc (WK [j + 1]) (R p)) (WK [j + 1]) ∨
        R i = pc (pc (WK [j + 1]) (pc (pc (MYP k) (R p)) (MYP (11 - k)))) (WK [j + 1])) := by
  unfold repRK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, d⟩ := mkA h
  refine ⟨_, _, _, Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.blt_eq.mp c, ?_⟩
  rcases mkIf d with ⟨-, d⟩ | ⟨-, d⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true d)
  · exact Or.inr (Nat.eq_of_beq_eq_true d)

theorem reps_memR {w : List Nat} (hw : lettersOK w = true) {R P : Nat → Nat} {n : Nat}
    (h0 : R 0 = WK w) (hr : ∀ i < n, 0 < i → repRK R P i = true) :
    ∀ i < n, ∃ c ∈ P1408, RepC (R i) (c * elemW w * c⁻¹) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · refine ⟨1, one_mem _, ?_⟩
      rw [h0]
      simpa using repC_word hw
    · obtain ⟨p, k, j, hp, hk, hj, e | e⟩ := repRK_parts (hr i hi hpos)
      · obtain ⟨c, hcP, hc⟩ := ih p hp (by omega)
        have hG := repC_word (lettersOK_gen hj)
        have hR := repC_pc (repC_pc hG hc) hG
        rw [← e] at hR
        refine ⟨elemW [j + 1] * c, mul_mem (elemW_mem _) hcP, ?_⟩
        convert hR using 1
        calc (elemW [j + 1] * c) * elemW w * (elemW [j + 1] * c)⁻¹
            = elemW [j + 1] * (c * elemW w * c⁻¹) * (elemW [j + 1])⁻¹ := by group
          _ = _ := by rw [gen_inv hj]
      · obtain ⟨c, hcP, hc⟩ := ih p hp (by omega)
        have hG := repC_word (lettersOK_gen hj)
        have hR := repC_pc (repC_pc hG (repC_pc (repC_pc (repC_yp (k := k) (by omega)) hc)
          (repC_yp (k := 11 - k) (by omega)))) hG
        rw [← e] at hR
        refine ⟨elemW [j + 1] * elemW y0Word ^ k * c,
          mul_mem (mul_mem (elemW_mem _) (pow_mem (elemW_mem _) k)) hcP, ?_⟩
        convert hR using 1
        calc (elemW [j + 1] * elemW y0Word ^ k * c) * elemW w *
              (elemW [j + 1] * elemW y0Word ^ k * c)⁻¹
            = elemW [j + 1] * (elemW y0Word ^ k * (c * elemW w * c⁻¹) * (elemW y0Word ^ k)⁻¹) *
                (elemW [j + 1])⁻¹ := by group
          _ = _ := by rw [gen_inv hj, y_inv (by omega)]

theorem class_geR {w : List Nat} {R S : Nat → Nat} {n cnt : Nat}
    (hreps : ∀ i < n, ∃ c ∈ P1408, RepC (R i) (c * elemW w * c⁻¹))
    (hs : ∀ m < cnt, sortAt R S n cnt m = true) : cnt ≤ (conjClass P1408 (elemW w)).ncard := by
  have H : ∀ i, ∃ r : Equiv.Perm (Fin 1408), i < n → r ∈ conjClass P1408 (elemW w) ∧
      RepC (R i) r := by
    intro i
    by_cases hi : i < n
    · obtain ⟨c, hcP, hcR⟩ := hreps i hi
      exact ⟨_, fun _ => ⟨⟨c, hcP, rfl⟩, hcR⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose r hr using H
  have hS : ∀ m < cnt, f16 (S m) 0 < n ∧ f16 (S m) 1 < 11 := by
    intro m hm
    have h1 := hs m hm
    unfold sortAt at h1
    simp only [strictB_app] at h1
    obtain ⟨a, h1⟩ := mkA h1
    obtain ⟨b, -⟩ := mkA h1
    exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b⟩
  obtain ⟨e, he⟩ : ∃ e : Nat → Equiv.Perm (Fin 1408), ∀ m, e m =
      elemW y0Word ^ f16 (S m) 1 * r (f16 (S m) 0) * (elemW y0Word ^ f16 (S m) 1)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hkey : ∀ m < cnt, keyK (R (f16 (S m) 0)) (f16 (S m) 1) = keyP (e m) := by
    intro m hm
    rw [he m]
    exact keyK_eq (hr _ (hS m hm).1).2 (by have := (hS m hm).2; omega)
  have hsucc : ∀ m, m + 1 < cnt → keyP (e m) < keyP (e (m + 1)) := by
    intro m hm
    have h1 := hs m (by omega)
    unfold sortAt at h1
    simp only [strictB_app] at h1
    obtain ⟨-, h1⟩ := mkA h1
    obtain ⟨-, h1⟩ := mkA h1
    have e1 : Nat.blt (m + 1) cnt = true := Nat.blt_eq.mpr hm
    rw [e1] at h1
    rw [← hkey m (by omega), ← hkey (m + 1) hm]
    exact Nat.blt_eq.mp h1
  have hmono : ∀ m m', m < m' → m' < cnt → keyP (e m) < keyP (e m') := by
    intro m m' hlt hm'
    induction m' with
    | zero => omega
    | succ m' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
      · exact (ih h' (by omega)).trans (hsucc m' hm')
      · rw [h']
        exact hsucc m' hm'
  have hinj : Set.InjOn e ↑(Finset.range cnt) := by
    intro m hm m' hm' hee
    have hm1 : m < cnt := Finset.mem_range.1 hm
    have hm2 : m' < cnt := Finset.mem_range.1 hm'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := hmono m m' hlt hm2
      rw [hee] at h1
      exact lt_irrefl _ h1
    · have h1 := hmono m' m hlt hm1
      rw [hee] at h1
      exact lt_irrefl _ h1
  have hsub : (↑((Finset.range cnt).image e) : Set (Equiv.Perm (Fin 1408))) ⊆
      conjClass P1408 (elemW w) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hx
    have hm1 : m < cnt := Finset.mem_range.1 hm
    obtain ⟨⟨c, hcP, hcr⟩, -⟩ := hr _ (hS m hm1).1
    refine ⟨elemW y0Word ^ f16 (S m) 1 * c, mul_mem (pow_mem (elemW_mem _) _) hcP, ?_⟩
    rw [he m, hcr]
    group
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_range] at h1

theorem b_reps : ∀ i < 200, ∃ c ∈ P1408, RepC (ClsB.R i) (c * elemW wordB * c⁻¹) := by
  have h0 := b_root
  unfold rootK at h0
  refine reps_memR (P := ClsB.P) (by decide) (Nat.eq_of_beq_eq_true h0)
    (repSl_all (len := 50) (ns := 4) (by norm_num) fun s hs => ?_)
  have h := b_rep_all s hs
  unfold bRep at h
  exact h

theorem class_b_ge : 2200 ≤ (conjClass P1408 elemB).ncard :=
  class_geR (S := ClsB.S) b_reps (sortSl_all (len := 550) (ns := 4) (by norm_num) fun s hs => by
    have h := b_srt_all s hs
    unfold bSort at h
    exact h)

theorem z1_reps : ∀ i < 4200, ∃ c ∈ P1408, RepC (ClsZ1.R i) (c * elemW wordZ₁ * c⁻¹) := by
  have h0 := z1_root
  unfold rootK at h0
  refine reps_memR (P := ClsZ1.P) (by decide) (Nat.eq_of_beq_eq_true h0)
    (repSl_all (len := 100) (ns := 42) (by norm_num) fun s hs => ?_)
  have h := z1_rep_all s hs
  unfold z1Rep at h
  exact h

theorem class_z1_ge : 46200 ≤ (conjClass P1408 elemZ₁).ncard :=
  class_geR (S := ClsZ1.S) z1_reps
    (sortSl_all (len := 2200) (ns := 21) (by norm_num) fun s hs => by
      have h := z1_srt_all s hs
      unfold z1Sort at h
      exact h)

end CFSG.KD.HN1408.ClsR

end
