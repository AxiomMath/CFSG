
module

public import Certificates.Kernel.Sporadic.Fi24G2g.Hard

public section

namespace CertificateChecks.KernelFi24G2g

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24Fix CertificateChecks.KernelFi24Orb
  CertificateChecks.KernelFi24G2e TauCeti TauCeti.Sporadic CFSG.KC.Fi24FixK CFSG.KC.Fi24FixS

open CFSG.Sporadic.Fi24 (R cls D24)
open CFSG.Sporadic.FischerOddCore (HardFacts rep7)
open CFSG.KD.Fi24Orb (NM NI)
open CFSG.KD.Fi24G2e (CWL OWN0 OWN1 OWV0 OWV1 LWL0 LWL1 LEN0 LEN1 LON0 LON1 TB0 TB1 TI0 TI1 NODE)
open CFSG.KD.Fi24G2d (W2B W2D F2B F2D)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction

section D

theorem _root_.CFSG.Sporadic.FischerOddCore.HardFacts.conj {r r' c : R} (h : HardFacts r') (hc : c * r * c⁻¹ = r') : HardFacts r := by
  obtain ⟨m, W, hW, hcnt⟩ := h
  have hr : r = c⁻¹ * r' * c := by rw [← hc]; group
  let f : Subgroup.centralizer ({r'} : Set R) →* Subgroup.centralizer ({r} : Set R) :=
    { toFun := fun x => ⟨c⁻¹ * x * c, by
        rw [Subgroup.mem_centralizer_singleton_iff, hr]
        have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
        calc c⁻¹ * ↑x * c * (c⁻¹ * r' * c) = c⁻¹ * (↑x * r') * c := by group
          _ = c⁻¹ * (r' * ↑x) * c := by rw [hx]
          _ = c⁻¹ * r' * c * (c⁻¹ * ↑x * c) := by group⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  refine ⟨m, f W, map_derivedSeries_le_derivedSeries f 4 ⟨W, hW, rfl⟩, ?_⟩
  rw [card_fixed_pts2] at hcnt ⊢
  rw [← hcnt]
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun k => ?_)
  rw [MulAction.toPerm_apply]
  have e1 : r • k = k ↔ r' • (c • k) = c • k := by
    rw [hr, mul_smul, mul_smul, inv_smul_eq_iff]
  have e2 : ((f W : Subgroup.centralizer ({r} : Set R)) : R) • k = k ↔
      (W : R) • (c • k) = c • k := by
    change (c⁻¹ * (W : R) * c) • k = k ↔ _
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  rw [e1, e2]

end D

theorem own0_eq : OWN0 = [37886, 22978, 22975, 22973] := own_vals.1

theorem own1_eq : OWN1 = [37886, 22978, 22975] := own_vals.2.1

theorem ρ_wp (w : List ℕ) :
    ρ (wp w) = (w.map fun g => ρ (g0 g)).prod := by
  rw [wp, map_list_prod, List.map_map]
  rfl

section Bind

variable (hP : PtRank)
include hP

theorem comm_letters {a b o : ℕ} (ha : a < 12) (ho : o < 306936)
    (hab : CFSG.KD.Fi24Fix.TG a o = o) (hb : cls (pk ho) = ρ (g0 b)) :
    Commute (ρ (g0 a)) (ρ (g0 b)) := by
  have hfix : ρ (g0 a) • pk ho = pk ho := by
    rw [smul_pk_letter hP ha]
    apply pk_congr
    rw [walk_cons, walk_nil, hab]
  have e := CFSG.Sporadic.Fi24.cls_smul_R (ρ (g0 a)) (pk ho)
  rw [hfix, hb] at e
  change ρ (g0 a) * ρ (g0 b) = ρ (g0 b) * ρ (g0 a)
  calc ρ (g0 a) * ρ (g0 b) = ρ (g0 a) * ρ (g0 b) * (ρ (g0 a))⁻¹ * ρ (g0 a) := by group
    _ = ρ (g0 b) * ρ (g0 a) := by rw [← e]

theorem hard_W2B : HardFacts (ρ (wp W2B)) := by
  obtain ⟨c0, c2, c4, c6⟩ := cls_own hP
  obtain ⟨l1, l2, l3, l4, l5⟩ := leaves_W2B
  have hlist : (OWN0.map fun o => cls (pkT o)) = [ρ (g0 0), ρ (g0 2), ρ (g0 4), ρ (g0 6)] := by
    rw [own0_eq]
    simp only [List.map_cons, List.map_nil]
    rw [pkT_eq (r := 37886) (by norm_num), pkT_eq (r := 22978) (by norm_num),
      pkT_eq (r := 22975) (by norm_num), pkT_eq (r := 22973) (by norm_num), c0, c2, c4, c6]
  have hfixo : ∀ a ∈ W2B, ∀ o ∈ OWN0, CFSG.KD.Fi24Fix.TG a o = o := by
    rw [own0_eq]
    decide +kernel
  have cm : ∀ a ∈ W2B, ∀ b ∈ W2B, Commute (ρ (g0 a)) (ρ (g0 b)) := by
    intro a ha b hb
    have ha12 : a < 12 := by simp [W2B] at ha; omega
    simp only [W2B, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact comm_letters hP ha12 (o := 37886) (by norm_num) (hfixo a ha _ (by simp [own0_eq])) c0
    · exact comm_letters hP ha12 (o := 22978) (by norm_num) (hfixo a ha _ (by simp [own0_eq])) c2
    · exact comm_letters hP ha12 (o := 22975) (by norm_num) (hfixo a ha _ (by simp [own0_eq])) c4
    · exact comm_letters hP ha12 (o := 22973) (by norm_num) (hfixo a ha _ (by simp [own0_eq])) c6
  have hLW : ∀ j < 6, ∀ g ∈ CFSG.KC.Fi24G2e.brayWord W2B (LWL0 j) (LEN0 j) (Nat.beq (LON0 j) 1),
      g < 12 := by
    have hl : ∀ j < 6, ∀ g ∈ LWL0 j, g < 12 := by decide +kernel
    intro j hj
    exact brayWord_lt (by decide) (hl j hj) _ _
  have hperm : ∀ j < 6, (OWN0.map (walk CFSG.KD.Fi24Fix.TG
      (CFSG.KC.Fi24G2e.brayWord W2B (LWL0 j) (LEN0 j) (Nat.beq (LON0 j) 1)))).Perm OWN0 := by
    have hdata : ∀ j < 6, ((List.range 4).map fun s => OWV0.getD (4 * j + s) 0).Perm OWN0 := by
      decide +kernel
    have hown : OWN0 = (List.range 4).map fun s => OWN0.getD s 0 := by
      rw [own0_eq]
      rfl
    intro j hj
    convert hdata j hj using 1
    conv_lhs => rw [hown]
    rw [List.map_map]
    refine List.map_congr_left fun s hs => ?_
    have hs4 : s < 4 := List.mem_range.1 hs
    have h := l2 (4 * j + s) (by omega)
    rw [show (4 * j + s) / 4 = j by omega, show (4 * j + s) % 4 = s by omega] at h
    exact h
  obtain ⟨W, hW, hcnt⟩ := hard_of hP (w := W2B) (own := OWN0) (n := 504) (m := 2) (FL := F2B)
    (LW := fun j => CFSG.KC.Fi24G2e.brayWord W2B (LWL0 j) (LEN0 j) (Nat.beq (LON0 j) 1))
    (TB := TB0) (TI := TI0) (node := NODE)
    (by rw [hlist, ρ_wp]; rfl)
    (by
      rw [hlist]
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true, imp_false, not_false_eq_true, implies_true]
      refine ⟨⟨cm 0 (by decide) 2 (by decide), cm 0 (by decide) 4 (by decide),
        cm 0 (by decide) 6 (by decide)⟩, ⟨cm 2 (by decide) 4 (by decide),
        cm 2 (by decide) 6 (by decide)⟩, cm 4 (by decide) 6 (by decide), fun _ h => h.elim⟩)
    (by rw [own0_eq]; decide)
    (fun k => by
      rw [fixed_iff_walk hP (by decide)]
      exact CFSG.KD.Fi24G2d.fix_W2B_iff _ (NM_lt k.isLt))
    (fun i hi => (CFSG.KD.Fi24G2d.F2B_spec i hi).1)
    (strict_inj CFSG.KD.Fi24G2d.F2B_lt) hLW l1 hperm l3 l4
    (by decide +kernel) (by decide +kernel) (by rw [l5]; norm_num)
  exact ⟨2, W, hW, hcnt⟩

theorem hard_W2D : HardFacts (ρ (wp W2D)) := by
  obtain ⟨c0, c2, c4, -⟩ := cls_own hP
  obtain ⟨l1, l2, l3, l4, l5⟩ := leaves_W2D
  have hlist : (OWN1.map fun o => cls (pkT o)) = [ρ (g0 0), ρ (g0 2), ρ (g0 4)] := by
    rw [own1_eq]
    simp only [List.map_cons, List.map_nil]
    rw [pkT_eq (r := 37886) (by norm_num), pkT_eq (r := 22978) (by norm_num),
      pkT_eq (r := 22975) (by norm_num), c0, c2, c4]
  have hfixo : ∀ a ∈ W2D, ∀ o ∈ OWN1, CFSG.KD.Fi24Fix.TG a o = o := by
    rw [own1_eq]
    decide +kernel
  have cm : ∀ a ∈ W2D, ∀ b ∈ W2D, Commute (ρ (g0 a)) (ρ (g0 b)) := by
    intro a ha b hb
    have ha12 : a < 12 := by simp [W2D] at ha; omega
    simp only [W2D, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact comm_letters hP ha12 (o := 37886) (by norm_num) (hfixo a ha _ (by simp [own1_eq])) c0
    · exact comm_letters hP ha12 (o := 22978) (by norm_num) (hfixo a ha _ (by simp [own1_eq])) c2
    · exact comm_letters hP ha12 (o := 22975) (by norm_num) (hfixo a ha _ (by simp [own1_eq])) c4
  have hLW : ∀ j < 6, ∀ g ∈ CFSG.KC.Fi24G2e.brayWord W2D (LWL1 j) (LEN1 j) (Nat.beq (LON1 j) 1),
      g < 12 := by
    have hl : ∀ j < 6, ∀ g ∈ LWL1 j, g < 12 := by decide +kernel
    intro j hj
    exact brayWord_lt (by decide) (hl j hj) _ _
  have hperm : ∀ j < 6, (OWN1.map (walk CFSG.KD.Fi24Fix.TG
      (CFSG.KC.Fi24G2e.brayWord W2D (LWL1 j) (LEN1 j) (Nat.beq (LON1 j) 1)))).Perm OWN1 := by
    have hdata : ∀ j < 6, ((List.range 3).map fun s => OWV1.getD (3 * j + s) 0).Perm OWN1 := by
      decide +kernel
    have hown : OWN1 = (List.range 3).map fun s => OWN1.getD s 0 := by
      rw [own1_eq]
      rfl
    intro j hj
    convert hdata j hj using 1
    conv_lhs => rw [hown]
    rw [List.map_map]
    refine List.map_congr_left fun s hs => ?_
    have hs3 : s < 3 := List.mem_range.1 hs
    have h := l2 (3 * j + s) (by omega)
    rw [show (3 * j + s) / 3 = j by omega, show (3 * j + s) % 3 = s by omega] at h
    exact h
  obtain ⟨W, hW, hcnt⟩ := hard_of hP (w := W2D) (own := OWN1) (n := 696) (m := 3) (FL := F2D)
    (LW := fun j => CFSG.KC.Fi24G2e.brayWord W2D (LWL1 j) (LEN1 j) (Nat.beq (LON1 j) 1))
    (TB := TB1) (TI := TI1) (node := NODE)
    (by rw [hlist, ρ_wp]; rfl)
    (by
      rw [hlist]
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true, imp_false, not_false_eq_true, implies_true]
      exact ⟨⟨cm 0 (by decide) 2 (by decide), cm 0 (by decide) 4 (by decide)⟩,
        cm 2 (by decide) 4 (by decide), fun _ h => h.elim⟩)
    (by rw [own1_eq]; decide)
    (fun k => by
      rw [fixed_iff_walk hP (by decide)]
      exact CFSG.KD.Fi24G2d.fix_W2D_iff _ (NM_lt k.isLt))
    (fun i hi => (CFSG.KD.Fi24G2d.F2D_spec i hi).1)
    (strict_inj CFSG.KD.Fi24G2d.F2D_lt) hLW l1 hperm l3 l4
    (by decide +kernel) (by decide +kernel) (by rw [l5]; norm_num)
  exact ⟨3, W, hW, hcnt⟩

theorem wit2078_facts :
    (∀ i < 7, Nat.card {x : D24 // rep7 i * x * (rep7 i)⁻¹ = x} =
      [3512, 3512, 504, 31672, 31672, 696, 696].getD i 0) ∧
    HardFacts (rep7 2) ∧ HardFacts (rep7 5) ∧ HardFacts (rep7 6) := by
  have hA : CWL 2 = W2B ∧ CWL 5 = W2D ∧ CWL 6 = W2D := by decide +kernel
  obtain ⟨c2, h2⟩ := conj_rep7 (i := 2) (by norm_num)
  obtain ⟨c5, h5⟩ := conj_rep7 (i := 5) (by norm_num)
  obtain ⟨c6, h6⟩ := conj_rep7 (i := 6) (by norm_num)
  rw [hA.1] at h2
  rw [hA.2.1] at h5
  rw [hA.2.2] at h6
  exact ⟨fun i hi => card_fixed_rep7 hP hi, (hard_W2B hP).conj h2, (hard_W2D hP).conj h5,
    (hard_W2D hP).conj h6⟩

end Bind

end CertificateChecks.KernelFi24G2g

end
