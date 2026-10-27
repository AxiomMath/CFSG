module

public import Certificates.Kernel.HN3.Data
public import CFSG.Certificates.Kernel.HN3OrbSound
public import CFSG.Sporadic.GLQ.HNTwoRank
public import CFSG.Sporadic.Recognition.HNMult3Words
public import CFSG.Sporadic.Recognition.HNMult3Data
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
import Certificates.Kernel.HN3.Prog
import Certificates.Kernel.HN3.Checks
import Certificates.Kernel.HN3.Tie
import Certificates.Kernel.HN3166.Seed
import Mathlib.Tactic.IntervalCases
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.Fam.Lin
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelHN3

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HN3 CFSG.KS.HN3 CFSG.KD.HN3 CFSG.KS.HNLocal CFSG.KC.HNF26729
  CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.HNTwoRank CFSG.Sporadic.Recognition.HNMult3


@[expose] noncomputable def gU (i : Fin 3) : GLHN := runProg (initRegs gA gB) hn3Prog (11 + i.val)

noncomputable def lt3 (c : ℕ) : GLHN :=
  cond (decide (c % 2 = 0)) (gU ⟨c / 2 % 3, Nat.mod_lt _ (by norm_num)⟩)
    (gU ⟨c / 2 % 3, Nat.mod_lt _ (by norm_num)⟩)⁻¹

theorem lt3_even (t : Fin 3) : lt3 (2 * t.val) = gU t := by
  have ht := t.isLt
  unfold lt3
  rw [show decide (2 * t.val % 2 = 0) = true by simp, cond_true]
  congr 1
  ext
  simp only
  omega

theorem lt3_odd (t : Fin 3) : lt3 (2 * t.val + 1) = (gU t)⁻¹ := by
  have ht := t.isLt
  unfold lt3
  rw [show decide ((2 * t.val + 1) % 2 = 0) = false by simp, cond_false]
  congr 2
  ext
  simp only
  omega

theorem lift_ofCodes3 (r : List ℕ) :
    FreeGroup.lift gU (FreeGroup.mk (ofCodes3 r)) = (r.map lt3).prod := by
  rw [FreeGroup.lift_mk]
  unfold ofCodes3
  rw [List.map_map]
  rfl

theorem hn3_facts :
    (∀ r ∈ hn3Rels, FreeGroup.lift gU (FreeGroup.mk r) = 1) ∧
    (∀ i, hn3Ord i = 0 → FreeGroup.lift gU (FreeGroup.mk (hn3Cw i)) = gU i) ∧
    (∀ i, hn3Ord i ≠ 0 → gU i ^ hn3Ord i = 1) ∧
    58320 ≤ Nat.card (Subgroup.closure (Set.range gU)) := by
  have hc := CFSG.KD.FamHNSeed.consts
  have cA : Canon 5 133 13 (CFSG.KD.FamHNSeed.RW 1) :=
    validM_canon (d := 133) (S := 1729) hc CertificateChecks.KernelHN.s_v1
  have cB : Canon 5 133 13 (CFSG.KD.FamHNSeed.RW 2) :=
    validM_canon (d := 133) (S := 1729) hc CertificateChecks.KernelHN.s_v2
  have hA : (CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Sporadic.HN.Native.seedA :
      Matrix (Fin 133) (Fin 133) (ZMod 5)) = OM (CFSG.KD.FamHNSeed.RW 1) :=
    CertificateChecks.KernelHN.s_mA
  have hB : (CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Sporadic.HN.Native.seedB :
      Matrix (Fin 133) (Fin 133) (ZMod 5)) = OM (CFSG.KD.FamHNSeed.RW 2) :=
    CertificateChecks.KernelHN.s_mB
  have hS1 : CFSG.Blueprint.NativeSporadic.HNSeed1 = CFSG.Sporadic.HN.Native.seedA := rfl
  have hS2 : CFSG.Blueprint.NativeSporadic.HNSeed2 = CFSG.Sporadic.HN.Native.seedB := rfl
  have eA : φ gA = OM (CFSG.KD.FamHNSeed.RW 1) := by
    rw [φ_gA, ← hA]
    change CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Blueprint.NativeSporadic.HNSeed1 = _
    rw [hS1]
  have eB : φ gB = OM (CFSG.KD.FamHNSeed.RW 2) := by
    rw [φ_gB, ← hB]
    change CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Blueprint.NativeSporadic.HNSeed2 = _
    rw [hS2]
  have hP : progK mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) CFSG.KD.FamHNSeed.ONE
      (hn3Prog.map codeHN3) regs = true := by
    rw [← prog_eq]
    exact prog_ok
  have hR := progK_sound hc φ cA cB eA eB prog_lt prog_noPwr hP
  have hlet : ∀ c < 6, Canon 5 133 13 (getN 0 regs c) ∧ OM (getN 0 regs c) = φ (lt3 c) := by
    intro c hc6
    obtain ⟨t, b, hb, rfl⟩ : ∃ t : Fin 3, ∃ b, b < 2 ∧ c = 2 * t.val + b :=
      ⟨⟨c / 2, by omega⟩, c % 2, Nat.mod_lt _ (by norm_num), by simp only; omega⟩
    obtain ⟨q1, q2, q3, q4⟩ := hR t.val t.isLt
    interval_cases b
    · rw [Nat.add_zero, lt3_even]
      exact ⟨q1, q3⟩
    · rw [lt3_odd]
      exact ⟨q2, q4⟩
  have hword : ∀ w : List ℕ, (∀ c ∈ w, c < 6) →
      φ (w.map lt3).prod = (w.map fun c => OM (getN 0 regs c)).prod := by
    intro w hw
    rw [map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun c hcw => ((hlet c (hw c hcw)).2).symm)
  obtain ⟨hrl, hg2, hg3, hg5⟩ := codes_lt
  have hrels := relsK_sound hc (G := regs) (rels := rels)
    (fun r hr c hcr => (hlet c (hrl r hr c hcr)).1) rels_ok
  have hmem : ∀ w ∈ hn3Rels ++ [hn3Cw 0 ++ [(0, false)], hn3Cw 1 ++ [(1, false)]],
      FreeGroup.lift gU (FreeGroup.mk w) = 1 := by
    intro w hw
    rw [← rels_eq, List.mem_map] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    rw [lift_ofCodes3]
    apply φ_injective
    rw [hword r (hrl r hr), hrels r hr, map_one]
  have hcw : ∀ i : Fin 3, hn3Cw i ++ [(i, false)] ∈
      hn3Rels ++ [hn3Cw 0 ++ [(0, false)], hn3Cw 1 ++ [(1, false)]] →
      FreeGroup.lift gU (FreeGroup.mk (hn3Cw i)) = gU i := by
    intro i hi
    have h := hmem _ hi
    have e : FreeGroup.lift gU (FreeGroup.mk [(i, false)]) = (gU i)⁻¹ := by
      rw [FreeGroup.lift_mk]
      simp
    rw [← FreeGroup.mul_mk, map_mul, e, mul_inv_eq_one] at h
    exact h
  refine ⟨fun r hr => hmem r (List.mem_append_left _ hr), fun i hi => ?_, fun i hi => ?_, ?_⟩
  · fin_cases i
    · exact hcw 0 (List.mem_append_right _ List.mem_cons_self)
    · exact hcw 1 (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact absurd hi (by decide)
  · fin_cases i
    · exact absurd rfl hi
    · exact absurd rfl hi
    · have h := hmem (ofCodes3 [4, 4]) (List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_cons_self (a := [4, 4]))))
      rw [lift_ofCodes3] at h
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
      rw [show (4 : ℕ) = 2 * (2 : Fin 3).val from rfl, lt3_even] at h
      change gU 2 ^ 2 = 1
      rw [pow_two]
      exact h
  · let K : Subgroup GLHN := Subgroup.closure (Set.range gU)
    have hgK : ∀ i, gU i ∈ K := fun i => Subgroup.subset_closure (Set.mem_range_self i)
    have hlK : ∀ c, lt3 c ∈ K := by
      intro c
      unfold lt3
      cases decide (c % 2 = 0)
      · rw [cond_false]
        exact K.inv_mem (hgK _)
      · rw [cond_true]
        exact hgK _
    have hk : ∀ gw : List (List ℕ), (∀ r ∈ gw, ∀ c ∈ r, c < 6) → ∀ j < gw.length,
        ((gw.getD j []).map lt3).prod ∈ K ∧
          φ ((gw.getD j []).map lt3).prod = ((gw.getD j []).map fun c => OM (getN 0 regs c)).prod := by
      intro gw hgw j hj
      have hm : gw.getD j [] ∈ gw := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      refine ⟨K.list_prod_mem fun x hx => ?_, hword _ (hgw _ hm)⟩
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      exact hlK c
    have hG : ∀ gw : List (List ℕ), (∀ r ∈ gw, ∀ c ∈ r, c < 6) →
        ∀ w ∈ gw, ∀ c ∈ w, Canon 5 133 13 (getN 0 regs c) :=
      fun gw hgw w hw c hcw => (hlet c (hgw w hw c hcw)).1
    have d2 := orbK_dvd hc (hG g2 hg2) orb2_ok φ K _ (hk g2 hg2)
    have d3 := orbK_dvd hc (hG g3 hg3) orb3_ok φ K _ (hk g3 hg3)
    have d5 := orbK_dvd hc (hG g5 hg5) orb5_ok φ K _ (hk g5 hg5)
    have h1 : 16 * 729 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d2 d3
    have h2 : 16 * 729 * 5 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 d5
    have hfin : Finite GLHN := Finite.of_injective
      (fun g : GLHN => fun i j => (g : Matrix (Fin 133) (Fin 133) (ZMod 5)) i j)
      (fun g h e => Units.ext (Matrix.ext fun i j => congrFun (congrFun e i) j))
    exact Nat.le_of_dvd Nat.card_pos h2

end CertificateChecks.KernelHN3

end
