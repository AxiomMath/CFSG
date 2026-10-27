
module

public import Certificates.Kernel.J4Count.Fix5Base1

public import Certificates.Kernel.J4Count.FiveM24
public import Certificates.Kernel.J4Count.Fix11
public import CFSG.Sporadic.J4.Struct.FixNormalizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Five

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.J4.Struct CertificateChecks.KernelSporSch
open CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4Five
open CertificateChecks.KernelJ4Q CFSG.QuasithinUnique.A5
open scoped Classical

section Orbits

theorem ncard_orbit_qA : (orbit H qA).ncard = 28336 := by
  obtain ⟨l, hl, hq⟩ := cover_qv qA_mem
  have hfc : RC.getD l 0 = 128 := by
    obtain ⟨⟨g, hg⟩, e⟩ := hq
    change g • qv l = qA at e
    rw [← fixCard_qv hl, ← fixCard_qA, ← e, fixCard_smul hg]
  have hl6 : l = 6 := by
    interval_cases l <;> first | rfl | exact absurd hfc (by decide)
  subst hl6
  rw [← sizes.2.2.2.2, orbit_eq_iff.2 hq]

theorem q1_ne_qA : q1Row ≠ qA := by
  intro h
  have e := ncard_orbit_q1
  rw [h, ncard_orbit_qA] at e
  exact absurd e (by norm_num)

end Orbits

theorem card_S1 :
    40 ≤ Nat.card S1 := by
  classical
  have : Finite J := KernelJ4Hub.finite_J
  have h1 := Subgroup.card_mul_index (stabilizer S0 q1Row)
  rw [index_stabilizer] at h1
  have horb : orbit S0 q1Row ⊆ ((x0PtSet.erase v).erase qA : Set Row) := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hgX := (Subgroup.mem_inf.1 hg).1
    have hgv : g • v = v := (Subgroup.mem_inf.1 hg).2
    change g • q1Row ∈ ((x0PtSet.erase v).erase qA : Set Row)
    obtain ⟨g₁, hg₁, hq⟩ := exists_of_mem_pts hM5 q1_mem_pts
    have hmem : g • q1Row ∈ x0PtSet := by
      rw [← hq, smul_smul]
      exact smul_mem_pts hM5 (X0Sub.mul_mem hgX hg₁)
    rw [Finset.coe_erase, Finset.coe_erase]
    refine ⟨⟨hmem, fun h => ?_⟩, fun h => ?_⟩
    · apply q1_ne_w₀
      have e : g • q1Row = g • v := (h : g • q1Row = v).trans hgv.symm
      rw [smul_left_cancel g e]
      exact v_eq_root
    · apply q1_ne_qA
      rw [← S0_fix_qA hg] at h
      exact smul_left_cancel g h
  have hcard : (orbit S0 q1Row).ncard ≤ 12 := by
    refine (Set.ncard_le_ncard horb (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    have hv : v ∈ x0PtSet := by rw [v_eq_root]; exact w₀_mem_pts hM5
    have hqA : qA ∈ x0PtSet.erase v := Finset.mem_erase.2 ⟨qA_ne_v, qA_mem_pts⟩
    rw [Finset.card_erase_of_mem hqA, Finset.card_erase_of_mem hv, card_x0PtSet]
  have hS1 : Nat.card (stabilizer S0 q1Row) = Nat.card S1 := by
    have hsub : S1.subgroupOf S0 = stabilizer S0 q1Row := by
      ext ⟨g, hg⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_stabilizer_iff]
      exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
    rw [← hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : S1 ≤ S0)).toEquiv
  rw [card_S0, hS1] at h1
  by_contra hlt
  have h2 : Nat.card S1 * (orbit S0 q1Row).ncard ≤ 39 * 12 := Nat.mul_le_mul (by omega) hcard
  omega

section Bound

theorem fix_cases5 {h : J} (hh : h ∈ H) (ho : orderOf h = 5) {w : Row} (hw : w ∈ orbit J v)
    (hf : h • w = w) :
    w = v ∨ (orbit H w).ncard = 28336 ∨ (orbit H w).ncard = 32643072 := by
  have hs := ncard_orbit_mem hw
  have hst := stab_mul_sz w
  have h5 : 5 ∣ Nat.card (stabilizer H w) := by
    have hm : (⟨h, hh⟩ : H) ∈ stabilizer H w := hf
    have := Subgroup.orderOf_dvd_natCard (stabilizer H w) hm
    rwa [← Subgroup.orderOf_coe, Subgroup.coe_mk, ho] at this
  have hdiv : Nat.card (stabilizer H w) = 501397585920 / (orbit H w).ncard :=
    (Nat.div_eq_of_eq_mul_left (L7_pos _ hs) hst.symm).symm
  rcases five_sizes _ hs (hdiv ▸ h5) with e | e | e
  · left
    have h0 : (orbit H v).ncard = 1 := by
      rw [← qv_zero]
      exact sz_zero
    obtain ⟨g, rfl⟩ := mem_orbit_of_ncard (mem_orbit_self v) hw (e.trans h0.symm)
    have hg : (g : J) ∈ stabilizer J v := by
      rw [stabilizer_v]
      exact g.2
    exact hg
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

theorem fiveElt_mem_H : fiveElt ∈ H := Hj_le_H fiveElt_mem_Hj

theorem card_centralizer_H_five :
    Nat.card (Subgroup.centralizer ({⟨fiveElt, fiveElt_mem_H⟩} : Set H)) ≤ 480 := by
  have hmap : (Subgroup.centralizer ({⟨fiveElt, fiveElt_mem_H⟩} : Set H)).map H.subtype =
      Subgroup.centralizer ({fiveElt} : Set J) ⊓ Hj := by
    rw [← H_eq_Hj']
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨centJ_iff.2 (coe_comm' ((mem_cent_iff' (G := ↥H)).1 hy)).symm, y.2⟩
    · rintro ⟨hx, hxH⟩
      refine ⟨⟨x, hxH⟩, (mem_cent_iff' (G := ↥H)).2 (Subtype.ext ?_), rfl⟩
      exact (centJ_iff.1 hx).symm
  have key := card_centralizer_fiveElt_Hj_le
  rw [← hmap, Subgroup.card_map_of_injective H.subtype_injective] at key
  exact key

theorem stab_card_of {q : Row} {s : ℕ} (hs : (orbit H q).ncard = s) (hs0 : 0 < s) :
    Nat.card (stabilizer H q) = 501397585920 / s := by
  have := stab_mul_sz q
  rw [hs] at this
  exact (Nat.div_eq_of_eq_mul_left hs0 this.symm).symm

theorem fix_orbit_le {q : Row} {s : ℕ} (hs : (orbit H q).ncard = s) (hs0 : 0 < s)
    (h25 : ¬ 25 ∣ 501397585920 / s) (hq : fiveElt • q = q) (hnq : nElt • q = q)
    (K : Subgroup J) (hKH : K ≤ H) (hKq : ∀ k ∈ K, k • q = q)
    (hKc : K ≤ Subgroup.centralizer ({fiveElt} : Set J)) :
    Nat.card {x : Row // x ∈ orbit H q ∧ fiveElt • x = x} * Nat.card K ≤ 480 := by
  have : Finite H := finite_H
  let xH : H := ⟨fiveElt, fiveElt_mem_H⟩
  let nH : H := ⟨nElt, by rw [← stabilizer_v]; exact nElt_fix_v⟩
  have hxo : orderOf xH = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_fiveElt hM5
  have hr : nH * xH * nH⁻¹ = xH ^ 2 := conj_sq_of_coe nElt_conj'
  have hc : Nat.card K ≤ Nat.card ↥(Subgroup.centralizer ({xH} : Set H) ⊓ stabilizer H q) := by
    refine Nat.card_le_card_of_injective (fun k => (⟨⟨k, hKH k.2⟩, ?_⟩ :
      ↥(Subgroup.centralizer ({xH} : Set H) ⊓ stabilizer H q))) ?_
    · refine Subgroup.mem_inf.2 ⟨(mem_cent_iff' (G := ↥H)).2 (Subtype.ext ?_), hKq k k.2⟩
      exact (centJ_iff.1 (hKc k.2)).symm
    · intro a b e
      exact Subtype.ext (congrArg (fun z : ↥(Subgroup.centralizer ({xH} : Set H) ⊓
        stabilizer H q) => ((z : H) : J)) e)
  have hq' : xH • q = q := hq
  have hnq' : nH • q = q := hnq
  have h25' : ¬ 25 ∣ Nat.card (stabilizer H q) := by rw [stab_card_of hs hs0]; exact h25
  have h := card_fix_mul_le (G := H) (X := Row) q hxo hq' hnq' hr h25' hc card_centralizer_H_five
  have e : Nat.card {x : Row // x ∈ orbit H q ∧ xH • x = x} =
      Nat.card {x : Row // x ∈ orbit H q ∧ fiveElt • x = x} := rfl
  rw [e] at h
  exact h

theorem card_fix_fiveElt_le :
    Nat.card {w : Row // w ∈ orbit J v ∧ fiveElt • w = w} ≤ 14 := by
  classical
  have hqA := fiveElt_smul_pts hM5 qA_mem_pts
  have hq1 := fiveElt_smul_pts hM5 q1_mem_pts
  have hA : Nat.card {x : Row // x ∈ orbit H qA ∧ fiveElt • x = x} ≤ 1 := by
    have h := fix_orbit_le ncard_orbit_qA (by norm_num) (by norm_num) hqA nElt_fix_qA S0
      (fun g hg => by rw [← stabilizer_v]; exact (Subgroup.mem_inf.1 hg).2)
      (fun g hg => S0_fix_qA hg)
      (fun g hg => X0Sub_le_centralizer hM5 (Subgroup.mem_inf.1 hg).1)
    rw [card_S0] at h
    omega
  have h1 : Nat.card {x : Row // x ∈ orbit H q1Row ∧ fiveElt • x = x} ≤ 12 := by
    have h := fix_orbit_le ncard_orbit_q1 (by norm_num) (by norm_num) hq1 nElt_fix_q1 S1
      (fun g hg => by rw [← stabilizer_v]; exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2)
      (fun g hg => (Subgroup.mem_inf.1 hg).2)
      (fun g hg => X0Sub_le_centralizer hM5 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).1)
    have h40 := card_S1
    by_contra hlt
    have : 13 * 40 ≤ Nat.card {x : Row // x ∈ orbit H q1Row ∧ fiveElt • x = x} * Nat.card S1 :=
      Nat.mul_le_mul (by omega) h40
    omega
  set F : Set Row := {w | w ∈ orbit J v ∧ fiveElt • w = w}
  set FA : Set Row := {x | x ∈ orbit H qA ∧ fiveElt • x = x}
  set F1 : Set Row := {x | x ∈ orbit H q1Row ∧ fiveElt • x = x}
  have hsub : F ⊆ {v} ∪ FA ∪ F1 := by
    rintro w ⟨hw, hf⟩
    rcases fix_cases5 fiveElt_mem_H (orderOf_fiveElt hM5) hw hf with rfl | hs | hs
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr ⟨mem_orbit_of_ncard qA_mem hw (hs.trans ncard_orbit_qA.symm), hf⟩)
    · exact Or.inr ⟨mem_orbit_of_ncard q1_mem hw (hs.trans ncard_orbit_q1.symm), hf⟩
  have : Finite H := finite_H
  have hfA : FA.Finite := (Set.finite_range fun g : H => g • qA).subset fun x hx => hx.1
  have hf1 : F1.Finite := (Set.finite_range fun g : H => g • q1Row).subset fun x hx => hx.1
  have hfin : ({v} ∪ FA ∪ F1 : Set Row).Finite := ((Set.finite_singleton v).union hfA).union hf1
  have eF : Nat.card {w : Row // w ∈ orbit J v ∧ fiveElt • w = w} = F.ncard := Nat.card_coe_set_eq _
  have eA : Nat.card {x : Row // x ∈ orbit H qA ∧ fiveElt • x = x} = FA.ncard := Nat.card_coe_set_eq _
  have e1 : Nat.card {x : Row // x ∈ orbit H q1Row ∧ fiveElt • x = x} = F1.ncard :=
    Nat.card_coe_set_eq _
  rw [eF]
  calc F.ncard ≤ ({v} ∪ FA ∪ F1 : Set Row).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ ({v} ∪ FA : Set Row).ncard + F1.ncard := Set.ncard_union_le _ _
    _ ≤ ({v} : Set Row).ncard + FA.ncard + F1.ncard :=
        Nat.add_le_add_right (Set.ncard_union_le _ _) _
    _ ≤ 1 + 1 + 12 := by
        rw [Set.ncard_singleton, ← eA, ← e1]
        omega
    _ = 14 := rfl

theorem card_centralizer_fiveElt_le :
    Nat.card (Subgroup.centralizer ({fiveElt} : Set J)) ≤ 6720 := by
  classical
  have : Finite J := KernelJ4Hub.finite_J
  set C : Subgroup J := Subgroup.centralizer ({fiveElt} : Set J) with hC
  have hfixv : fiveElt • v = v := by
    have : fiveElt ∈ stabilizer J v := by rw [stabilizer_v]; exact fiveElt_mem_H
    exact this
  have horb : orbit C v ⊆ {w : Row | w ∈ orbit J v ∧ fiveElt • w = w} := by
    rintro _ ⟨⟨c, hc⟩, rfl⟩
    have hcc : fiveElt * c = c * fiveElt := centJ_iff.1 hc
    refine ⟨⟨c, rfl⟩, ?_⟩
    change fiveElt • (c • v) = c • v
    rw [smul_smul, hcc, mul_smul, hfixv]
  have hfinF : ({w : Row | w ∈ orbit J v ∧ fiveElt • w = w}).Finite :=
    (Set.finite_range fun g : J => g • v).subset fun w hw => hw.1
  have hO : (orbit C v).ncard ≤ 14 := by
    refine (Set.ncard_le_ncard horb hfinF).trans ?_
    rw [← Nat.card_coe_set_eq]
    exact card_fix_fiveElt_le
  have hS : Nat.card (stabilizer C v) ≤ 480 := by
    have hsub : (C ⊓ Hj).subgroupOf C = stabilizer C v := by
      ext ⟨g, hg⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_stabilizer_iff]
      rw [← H_eq_Hj', ← stabilizer_v]
      exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
    rw [← hsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ⊓ Hj ≤ C)).toEquiv]
    exact card_centralizer_fiveElt_Hj_le
  have h1 := Subgroup.card_mul_index (stabilizer C v)
  rw [index_stabilizer] at h1
  rw [← h1]
  calc Nat.card (stabilizer C v) * (orbit C v).ncard ≤ 480 * 14 := Nat.mul_le_mul hS hO
    _ = 6720 := rfl

theorem centralizer_fiveElt_eq' : Subgroup.centralizer ({fiveElt} : Set J) = X0Sub := by
  have : Finite J := KernelJ4Hub.finite_J
  refine (Subgroup.eq_of_le_of_card_ge (X0Sub_le_centralizer hM5) ?_).symm
  rw [card_X0Sub hM5]
  exact card_centralizer_fiveElt_le

end Bound

end CertificateChecks.KernelJ4Count.Five

end
