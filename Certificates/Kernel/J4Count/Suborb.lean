
module

public import Certificates.Kernel.J4Count.SuborbBase1

public import Certificates.Kernel.J4Count.FixZ
public import Certificates.Kernel.J4Count.ChecksQ1
public import Certificates.Kernel.J4Hub.Struct
public import Certificates.Kernel.J4Q.Mat
public import CFSG.Sporadic.J4.QT2LocX0CentMainBase1
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.J4.Struct CertificateChecks.KernelSporSch

section Dvd

variable {G X : Type*} [Group G] [Finite G] [MulAction G X]

end Dvd

theorem fixCard_qv {l : ℕ} (hl : l < 7) : fixCard (qv l) = RC.getD l 0 := by
  rw [fixCard_rep hl]
  interval_cases l <;> rfl

theorem dc_exact : ∃ wr : Fin 6 → J, (∀ g : J, ∃ o : Option (Fin 6), g ∈ dcSet H (wO wr o)) ∧
    ∀ o : Option (Fin 6), (dcSet H (wO wr o)).ncard = Nat.card H * nO KernelJ4Hub.nD o := by
  have : Finite J := KernelJ4Hub.finite_J
  have : Fintype J := Fintype.ofFinite J
  obtain ⟨-, wr, hcov, hsz⟩ := KernelJ4Hub.dc_data
  obtain ⟨hex, -, -⟩ := dcF_exact (w := fun i => wr i.val) hcov hsz KernelJ4Hub.card_K_le
  rw [← H_eq_Kz] at hex hcov
  refine ⟨fun i => wr i.val, fun g => ?_, fun o => ?_⟩
  · rcases hcov g with h | ⟨i, h⟩
    · exact ⟨none, by rw [wO, Option.elim_none, dcSet_one]; exact h⟩
    · exact ⟨some i, h⟩
  · rw [← card_dcF]
    exact hex o

theorem orbit_card_of {wr : Fin 6 → J}
    (hsz : ∀ o : Option (Fin 6), (dcSet H (wO wr o)).ncard = Nat.card H * nO KernelJ4Hub.nD o)
    {g : J} {o : Option (Fin 6)} (hg : g ∈ dcSet H (wO wr o)) :
    (orbit H (g • v)).ncard = nO KernelJ4Hub.nD o := by
  have : Finite J := KernelJ4Hub.finite_J
  have e := dcSet_eq_of_mem (mem_dcSet_self H g) hg
  have h1 := ncard_dcSet_eq H v stabilizer_v g
  rw [e, hsz o] at h1
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm

theorem ncard_orbit_mem {w : Row} (hw : w ∈ orbit J v) : (orbit H w).ncard ∈ L7 := by
  obtain ⟨wr, hcov, hsz⟩ := dc_exact
  obtain ⟨g, rfl⟩ := hw
  obtain ⟨o, ho⟩ := hcov g
  change (orbit H (g • v)).ncard ∈ L7
  rw [orbit_card_of hsz ho]
  exact nO_mem o

theorem mem_orbit_of_ncard {p q : Row} (hp : p ∈ orbit J v) (hq : q ∈ orbit J v)
    (h : (orbit H q).ncard = (orbit H p).ncard) : q ∈ orbit H p := by
  obtain ⟨wr, hcov, hsz⟩ := dc_exact
  obtain ⟨g, rfl⟩ := hp
  obtain ⟨g', rfl⟩ := hq
  obtain ⟨o, ho⟩ := hcov g
  obtain ⟨o', ho'⟩ := hcov g'
  change (orbit H (g' • v)).ncard = (orbit H (g • v)).ncard at h
  rw [orbit_card_of hsz ho, orbit_card_of hsz ho'] at h
  have e := nO_inj h
  subst e
  change g' • v ∈ orbit H (g • v)
  rw [smul_mem_orbit_iff H v stabilizer_v, dcSet_eq_of_mem (mem_dcSet_self H g) ho]
  exact ho'

theorem eq_of_mem_orbit_qv {l m : ℕ} (hl : l < 7) (hm : m < 7)
    (h : qv m ∈ orbit H (qv l)) : l = m := by
  obtain ⟨⟨g, hg⟩, e⟩ := h
  change g • qv l = qv m at e
  have h1 : fixCard (qv m) = fixCard (qv l) := by rw [← e, fixCard_smul hg]
  have h2 : bilV (qv m) = bilV (qv l) := by rw [← e, bilV_smul hg]
  have h1' : repCounts[m]! = repCounts[l]! := (fixCard_rep hm).symm.trans (h1.trans (fixCard_rep hl))
  have e2 := repCounts_cases ⟨l, hl⟩ ⟨m, hm⟩ h1' (fun hl2 hm3 => ?_) (fun hl3 hm2 => ?_)
  · exact congrArg Fin.val e2
  · subst hl2 hm3
    have h2' : bilV (toRow (toVecD 112 repVecs[3]!)) = bilV (toRow (toVecD 112 repVecs[2]!)) := h2
    rw [bilV_rep_two, bilV_rep_three] at h2'
    exact absurd h2' (by decide)
  · subst hl3 hm2
    have h2' : bilV (toRow (toVecD 112 repVecs[2]!)) = bilV (toRow (toVecD 112 repVecs[3]!)) := h2
    rw [bilV_rep_two, bilV_rep_three] at h2'
    exact absurd h2' (by decide)

theorem sz_mem {l : ℕ} (hl : l < 7) : sz l ∈ L7 := ncard_orbit_mem (qv_mem hl)

theorem sz_ne {l m : ℕ} (hl : l < 7) (hm : m < 7) (hlm : l ≠ m) :
    sz l ≠ sz m := fun e => hlm (eq_of_mem_orbit_qv hl hm
  (mem_orbit_of_ncard (qv_mem hl) (qv_mem hm) e.symm))

theorem sz_zero : sz 0 = 1 := by
  have hst : stabilizer H (qv 0) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (g : J) ∈ stabilizer J v := by
      rw [stabilizer_v]
      exact g.2
    rw [mem_stabilizer_iff, qv_zero]
    exact hg
  change (orbit H (qv 0)).ncard = 1
  rw [← index_stabilizer, hst, Subgroup.index_top]

theorem sz_dvd {l : ℕ} (hl : l < 7) :
    2048 ∣ sz l * RC.getD l 0 ∧ sz l * RC.getD l 0 ∣ 501397585920 := by
  have : Finite H := finite_H
  have h1 := dvd_orbit_left (G := H) (N.subgroupOf H) (qv l)
  have h2 := dvd_orbit_right (G := H) (N.subgroupOf H) (qv l)
  rw [card_NH, card_NH_stab, fixCard_qv hl] at h1
  rw [card_NH_stab, fixCard_qv hl, card_H'] at h2
  exact ⟨h1, h2⟩

theorem exists_sz {x : ℕ} (hx : x ∈ L7) : ∃ l < 7, sz l = x := by
  classical
  have hsub : (Finset.range 7).image sz ⊆ L7.toFinset := fun y hy => by
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
    exact List.mem_toFinset.2 (sz_mem (Finset.mem_range.1 hl))
  have hcard : L7.toFinset.card ≤ ((Finset.range 7).image sz).card := by
    rw [List.toFinset_card_of_nodup L7_nodup, Finset.card_image_of_injOn]
    · simp [L7]
    · intro l hl m hm e
      by_contra hne
      exact sz_ne (Finset.mem_range.1 hl) (Finset.mem_range.1 hm) hne e
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hx' : x ∈ (Finset.range 7).image sz := heq ▸ List.mem_toFinset.2 hx
  obtain ⟨l, hl, e⟩ := Finset.mem_image.1 hx'
  exact ⟨l, Finset.mem_range.1 hl, e⟩

theorem cover_qv {w : Row} (hw : w ∈ orbit J v) :
    ∃ l < 7, w ∈ orbit H (qv l) := by
  obtain ⟨l, hl, e⟩ := exists_sz (ncard_orbit_mem hw)
  exact ⟨l, hl, mem_orbit_of_ncard (qv_mem hl) hw e.symm⟩

theorem Hj_le_H : Hj ≤ H := by
  intro g hg
  rw [← stabilizer_v, mem_stabilizer_iff, v_eq_root]
  exact Hj_fix_root CertificateChecks.KernelJ4Q.matFacts g hg

theorem ncard_orbit_q1 :
    (orbit H CFSG.Sporadic.J4.QT2.q1Row).ncard = 32643072 := by
  have : Finite H := finite_H
  have hK := CFSG.Sporadic.J4.QT2.KSub_le CertificateChecks.KernelJ4Q.matFacts
  have hKH : CFSG.Sporadic.J4.QT2.KSub ≤ H := hK.trans (inf_le_left.trans Hj_le_H)
  have hle : CFSG.Sporadic.J4.QT2.KSub.subgroupOf H ≤
      stabilizer H CFSG.Sporadic.J4.QT2.q1Row := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    exact (Subgroup.mem_inf.1 (hK hg)).2
  have h := dvd_orbit_of_le (G := H) _ _ hle
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv,
    CFSG.Sporadic.J4.QT2.card_KSub CertificateChecks.KernelJ4Q.matFacts, card_H'] at h
  have h1 := dvd_orbit_left (G := H) (N.subgroupOf H) CFSG.Sporadic.J4.QT2.q1Row
  rw [card_NH, card_NH_stab, fixCard_q1] at h1
  have hm := ncard_orbit_mem q1_mem
  have key : ∀ a ∈ L7, 2048 ∣ a * 2 → a * 15360 ∣ 501397585920 → a = 32643072 := by decide
  exact key _ hm h1 h

theorem sz_one :
    sz 1 = 32643072 := by
  obtain ⟨l, hl, hq⟩ := cover_qv q1_mem
  have hfc : RC.getD l 0 = 2 := by
    obtain ⟨⟨g, hg⟩, e⟩ := hq
    change g • qv l = CFSG.Sporadic.J4.QT2.q1Row at e
    rw [← fixCard_qv hl, ← fixCard_q1, ← e, fixCard_smul hg]
  have hl1 : l = 1 := by
    interval_cases l <;> first | rfl | exact absurd hfc (by decide)
  subst hl1
  rw [← ncard_orbit_q1, orbit_eq_iff.2 hq]

theorem sizes :
    sz 0 = 1 ∧ sz 1 = 32643072 ∧ sz 4 = 3400320 ∧ sz 5 = 15180 ∧ sz 6 = 28336 := by
  have d2 := (sz_dvd (l := 2) (by norm_num)).1
  have d3 := (sz_dvd (l := 3) (by norm_num)).1
  have d4 := sz_dvd (l := 4) (by norm_num)
  have d5 := sz_dvd (l := 5) (by norm_num)
  have d6 := sz_dvd (l := 6) (by norm_num)
  have s1 := sz_one
  have n1 : ∀ m < 7, m ≠ 1 → sz m ≠ 32643072 := fun m hm h1 => by
    rw [← s1]
    exact sz_ne hm (by norm_num) h1
  have h := sizes_forced _ (sz_mem (by norm_num)) d2 (n1 2 (by norm_num) (by norm_num))
    _ (sz_mem (by norm_num)) d3 (n1 3 (by norm_num) (by norm_num))
      (sz_ne (by norm_num) (by norm_num) (by norm_num))
    _ (sz_mem (by norm_num)) d4.1 d4.2 (n1 4 (by norm_num) (by norm_num))
      (sz_ne (by norm_num) (by norm_num) (by norm_num)) (sz_ne (by norm_num) (by norm_num) (by norm_num))
    _ (sz_mem (by norm_num)) d5.1 d5.2 (n1 5 (by norm_num) (by norm_num))
      (sz_ne (by norm_num) (by norm_num) (by norm_num)) (sz_ne (by norm_num) (by norm_num) (by norm_num))
      (sz_ne (by norm_num) (by norm_num) (by norm_num))
    _ (sz_mem (by norm_num)) d6.1 d6.2 (n1 6 (by norm_num) (by norm_num))
      (sz_ne (by norm_num) (by norm_num) (by norm_num)) (sz_ne (by norm_num) (by norm_num) (by norm_num))
      (sz_ne (by norm_num) (by norm_num) (by norm_num)) (sz_ne (by norm_num) (by norm_num) (by norm_num))
  exact ⟨sz_zero, s1, h⟩

end CertificateChecks.KernelJ4Count

end
