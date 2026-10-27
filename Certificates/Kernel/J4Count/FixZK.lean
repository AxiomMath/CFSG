
module


public import Certificates.Kernel.J4Count.Suborb

public section

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.KC.J4Count

theorem card_fix_z : Nat.card {w : Row // w ∈ orbit J v ∧ z • w = w} = 52349 := by
  classical
  have : Finite J := CertificateChecks.KernelJ4Hub.finite_J
  have hfinO : (orbit J v).Finite := Set.finite_range _
  set F : Set Row := {w | w ∈ orbit J v ∧ z • w = w}
  set Fl : ℕ → Set Row := fun l => {w | w ∈ orbit H (qv l) ∧ z • w = w}
  have hFl_sub : ∀ l < 7, Fl l ⊆ F := fun l hl w hw => ⟨orbit_H_subset hl hw.1, hw.2⟩
  have hfinF : F.Finite := hfinO.subset fun w hw => hw.1
  have hfinFl : ∀ l < 7, (Fl l).Finite := fun l hl => hfinF.subset (hFl_sub l hl)
  have hU : hfinF.toFinset = (Finset.range 7).biUnion fun l =>
      if hl : l < 7 then (hfinFl l hl).toFinset else ∅ := by
    ext w
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro hw
      obtain ⟨l, hl, hwl⟩ := cover_qv hw.1
      exact ⟨l, hl, by rw [dif_pos hl, Set.Finite.mem_toFinset]; exact ⟨hwl, hw.2⟩⟩
    · rintro ⟨l, hl, hw⟩
      rw [dif_pos hl, Set.Finite.mem_toFinset] at hw
      exact hFl_sub l hl hw
  have hdisj : (↑(Finset.range 7) : Set ℕ).PairwiseDisjoint fun l =>
      if hl : l < 7 then (hfinFl l hl).toFinset else ∅ := by
    intro l hl l' hl' hne
    have hl7 : l < 7 := Finset.mem_range.1 hl
    have hl7' : l' < 7 := Finset.mem_range.1 hl'
    simp only [Function.onFun, dif_pos hl7, dif_pos hl7']
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [Set.Finite.mem_toFinset] at hw hw'
    have e : orbit H (qv l') = orbit H (qv l) := by
      rw [← orbit_eq_iff.2 hw.1, ← orbit_eq_iff.2 hw'.1]
    exact hne (eq_of_mem_orbit_qv hl7 hl7' (e ▸ mem_orbit_self (qv l')))
  have hcard : ∀ l (hl : l < 7), (hfinFl l hl).toFinset.card * 1771 = sz l * CZ.getD l 0 := by
    intro l hl
    rw [← card_fix_z_suborbit hl, ← Set.ncard_eq_toFinset_card _ (hfinFl l hl),
      ← Nat.card_coe_set_eq]
    rfl
  rw [show Nat.card {w : Row // w ∈ orbit J v ∧ z • w = w} = hfinF.toFinset.card by
    rw [← Set.ncard_eq_toFinset_card _ hfinF, ← Nat.card_coe_set_eq]; rfl, hU,
    Finset.card_biUnion hdisj]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  obtain ⟨s0, s1, s4, s5, s6⟩ := sizes
  have c0 := hcard 0 (by norm_num)
  have c1 := hcard 1 (by norm_num)
  have c2 := hcard 2 (by norm_num)
  have c3 := hcard 3 (by norm_num)
  have c4 := hcard 4 (by norm_num)
  have c5 := hcard 5 (by norm_num)
  have c6 := hcard 6 (by norm_num)
  rw [s0] at c0
  rw [s1] at c1
  rw [s4] at c4
  rw [s5] at c5
  rw [s6] at c6
  simp only [CZ, List.getD_cons_zero, List.getD_cons_succ, mul_zero] at c0 c1 c2 c3 c4 c5 c6
  simp only [show (0 : ℕ) < 7 by norm_num, show (1 : ℕ) < 7 by norm_num,
    show (2 : ℕ) < 7 by norm_num, show (3 : ℕ) < 7 by norm_num, show (4 : ℕ) < 7 by norm_num,
    show (5 : ℕ) < 7 by norm_num, show (6 : ℕ) < 7 by norm_num, dif_pos]
  omega

theorem card_fix_tJ :
    Nat.card {w : Row // w ∈ orbit J v ∧ CFSG.Quasithin.H13.J4.tJ • w = w} = 52349 := by
  rw [CFSG.Sporadic.J4.Struct.card_fix_conj (orbit J v)
    (fun g x hx => by obtain ⟨k, rfl⟩ := hx; exact ⟨g * k, mul_smul g k v⟩)
    CFSG.Quasithin.H13.J4.isConj_tJ_e1]
  exact card_fix_z

end CertificateChecks.KernelJ4Count

end
