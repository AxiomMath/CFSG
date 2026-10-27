
module

public import Certificates.Kernel.LyBenes.Facts
public import Certificates.Kernel.LyBase.Chain
public import Certificates.Kernel.LyBase.F2A
public import Certificates.Kernel.LyBase.F2B
public import Certificates.Kernel.LyBase.F2C
public import Certificates.Kernel.LyBase.F2D
public import CFSG.Certificates.Kernel.LyBase.Sound
public import CFSG.Certificates.Kernel.LyBase.Stab
import all CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs
import all CFSG.Sporadic.Recognition.LyonsFinalFamiliesBase
public import CFSG.Sporadic.Recognition.LyonsFinalB

public section

namespace CertificateChecks.KernelLyBase

open Equiv MulAction CFSG.KC CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.YModel.Sem CFSG.KC.LyGlue
  CFSG.KC.LyBase CFSG.KC.LyBenes CFSG.KC.MonsterConv.Perm
  CertificateChecks.KernelLy CertificateChecks.KernelLyB CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.CosetTable

noncomputable def rho (j : Nat) : Perm (Fin Ly0.deg) := Ly0.wG Ly0.gens0 (jZ j)

section Letters

variable (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
  (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat))
include hc hd

theorem nrep_rho : ∀ j < 6, NRep 17 Ly0.deg (NS j) (rho j) := by
  intro j hj
  interval_cases j
  · have e : rho 0 = Ly0.letterG Ly0.gens0 1 := by simp [rho, jZ]
    rw [e]
    exact nrep_z hc hd 1 (by decide)
  · have e : rho 1 = Ly0.letterG Ly0.gens0 2 := by simp [rho, jZ]
    rw [e]
    exact nrep_z hc hd 2 (by decide)
  · have e : rho 2 = Ly0.letterG Ly0.gens0 (-2) := by simp [rho, jZ]
    rw [e]
    exact nrep_z hc hd (-2) (by decide)
  · have e : rho 3 = gB 2 := by simp [rho, jZ, gB]
    rw [e]
    exact nrep_gen hc hd (by decide) gen_parts.1
  · have e : rho 4 = gB 3 := by simp [rho, jZ, gB]
    rw [e]
    exact nrep_gen hc hd (by decide) gen_parts.2.1
  · have e : rho 5 = gB 4 := by simp [rho, jZ, gB]
    rw [e]
    exact nrep_gen hc hd (by decide) gen_parts.2.2

omit hc hd in
theorem prod_rho : ∀ w : List Nat, (w.map rho).prod = Ly0.wG Ly0.gens0 (wZ w)
  | [] => by simp [wZ]
  | j :: w => by
    have e : wZ (j :: w) = jZ j ++ wZ w := by simp [wZ]
    rw [List.map_cons, List.prod_cons, prod_rho w, e, Ly0.wG_append]
    rfl

omit hc hd in
theorem wZ_mem (w : List Nat) : ∀ l ∈ wZ w, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hl
  exact jZ_mem j l hj

omit hc hd in
theorem wG_wZ_mem (w : List Nat) : Ly0.wG Ly0.gens0 (wZ w) ∈ Ly0.B0 :=
  Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem _ (wZ_mem w)

theorem compN_wZ {w : List Nat} (hw : ∀ j ∈ w, j < 6) (a : Fin Ly0.deg) :
    compN 17 (w.map NS) a = (Ly0.wG Ly0.gens0 (wZ w) a : Nat) := by
  rw [← prod_rho]
  exact compN_map NS rho w (fun j hj => nrep_rho hc hd j (hw j hj)) a

theorem rho_letIdx (l : Fin 6 × Bool) (hl : l.1.val < 5) :
    rho (letIdx l) = if l.2 then gB l.1 else (gB l.1)⁻¹ := by
  have h1 := nrep_rho hc hd (letIdx l) (letIdx_lt l hl)
  have h2 := nrep_letter hc hd l hl
  exact Equiv.ext fun a => Fin.ext ((h1 a).symm.trans (h2 a))

theorem lift_gB_eq_wG {r : List (Fin 6 × Bool)} (hb : isBWord r = true) :
    FreeGroup.lift gB (FreeGroup.mk r) = Ly0.wG Ly0.gens0 (wZ (r.map letIdx)) := by
  rw [lift_mk_eq_prod, ← prod_rho, List.map_map]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  unfold isBWord at hb
  exact (rho_letIdx hc hd l (of_decide_eq_true (List.all_eq_true.1 hb l hl))).symm

theorem rb_eq_one : ∀ r ∈ RB, FreeGroup.lift gB (FreeGroup.mk r) = 1 := fun r hr =>
  lift_gB_of_bNetOK hc hd (List.all_eq_true.1 rb_all r hr)

theorem cG_mul_cG : Ly0.cG * Ly0.cG = 1 := by
  have h := rb_eq_one hc hd (parseWord "cc") (by decide +kernel)
  have e : parseWord "cc" = [(0, true), (0, true)] := by decide +kernel
  have g0 : gB 0 = Ly0.cG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_zero]
  rw [e, lift_mk_eq_prod] at h
  simpa [g0] using h

theorem dG_pow_three : Ly0.dG ^ 3 = 1 := by
  have h := rb_eq_one hc hd (parseWord "ddd") (by decide +kernel)
  have e : parseWord "ddd" = [(1, true), (1, true), (1, true)] := by decide +kernel
  have g1 : gB 1 = Ly0.dG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_one]
  rw [e, lift_mk_eq_prod] at h
  rw [pow_three]
  simpa [g1] using h

omit hc hd in
theorem lift_comp_mk {G : Type*} [Group G] {m m' : Nat} (σ : Fin m → Fin m') (g : Fin m' → G) :
    ∀ w : List (Fin m × Bool), FreeGroup.lift (fun j => g (σ j)) (FreeGroup.mk w) =
      FreeGroup.lift g (FreeGroup.mk (w.map fun l => (σ l.1, l.2)))
  | [] => by simp [← FreeGroup.one_eq_mk]
  | l :: w => by
    have e1 : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
    have e2 : FreeGroup.mk ((σ l.1, l.2) :: w.map fun l => (σ l.1, l.2)) =
        FreeGroup.mk [(σ l.1, l.2)] * FreeGroup.mk (w.map fun l => (σ l.1, l.2)) := rfl
    rw [e1, List.map_cons, e2, map_mul, map_mul, lift_mk_single, lift_mk_single,
      lift_comp_mk σ g w]

theorem card_B0_le (hbc : RB5Bound) : Nat.card Ly0.B0 ≤ 5388768000 := by
  have hrel : ∀ r ∈ {r : FreeGroup (Fin (subsetOf 6 [0, 1, 2, 3, 4]).length) |
      r ∈ RB5.map FreeGroup.mk},
      FreeGroup.lift (fun j => gBs ((subsetOf 6 [0, 1, 2, 3, 4]).get j)) r = 1 := by
    intro r hr
    simp only [Set.mem_setOf_eq, List.mem_map, restrictWords, List.mem_filterMap] at hr
    obtain ⟨w', ⟨w, hw, hren⟩, rfl⟩ := hr
    rw [lift_comp_mk, map_renumber _ w w' hren]
    apply Subtype.ext
    rw [coe_lift_gBs]
    exact rb_eq_one hc hd w hw
  let φ := PresentedGroup.toGroup hrel
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Subgroup.closure_closure_coe_preimage,
      Subgroup.closure_le]
    rintro ⟨x, hx⟩ hx'
    have e0 : (subsetOf 6 [0, 1, 2, 3, 4]).get ⟨0, by decide⟩ = 0 := by decide
    have e1 : (subsetOf 6 [0, 1, 2, 3, 4]).get ⟨1, by decide⟩ = 1 := by decide
    have g0 : gB 0 = Ly0.cG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_zero]
    have g1 : gB 1 = Ly0.dG := by simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_one]
    rcases hx' with h | h
    · refine ⟨PresentedGroup.of ⟨0, by decide⟩, ?_⟩
      rw [PresentedGroup.toGroup.of, e0]
      exact Subtype.ext (g0.trans h.symm)
    · refine ⟨PresentedGroup.of ⟨1, by decide⟩, ?_⟩
      rw [PresentedGroup.toGroup.of, e1]
      exact Subtype.ext (g1.trans (Set.mem_singleton_iff.1 h).symm)
  have : Finite (PG _ RB5) := hbc.1
  exact (Nat.card_le_card_of_surjective φ hsurj).trans hbc.2

abbrev p0 : Fin Ly0.deg := ⟨0, by decide⟩

abbrev p3 : Fin Ly0.deg := ⟨3, by decide⟩

abbrev p1 : Fin Ly0.deg := ⟨1, by decide⟩

omit hc hd in
theorem nets_valid {L : List (List Nat)} (hL : ∀ w ∈ L, ∀ j ∈ w, j < 6) :
    ∀ Ns ∈ L.map (fun w => w.map NS), ∀ N ∈ Ns, StagesValid 17 N := by
  intro Ns hNs N hN
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hNs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hN
  exact valid_all j (hL w hw j hj)

theorem nets_act {L : List (List Nat)} (hL : ∀ w ∈ L, ∀ j ∈ w, j < 6)
    (K : Subgroup (Perm (Fin Ly0.deg))) (hK : ∀ w ∈ L, Ly0.wG Ly0.gens0 (wZ w) ∈ K) :
    ∀ Ns ∈ L.map (fun w => w.map NS), ∃ g ∈ K, ∀ a : Fin Ly0.deg, compN 17 Ns a = (g a : Nat) := by
  intro Ns hNs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hNs
  exact ⟨_, hK w hw, compN_wZ hc hd (hL w hw)⟩

theorem wG_fix {w : List Nat} {bs : List Nat} (h : fixAll cL dL bs w = true) (b : Fin Ly0.deg)
    (hb : (b : Nat) ∈ bs) : Ly0.wG Ly0.gens0 (wZ w) b = b := by
  have e := fixAll_sound bs h b hb
  rw [jwPt_wG hc hd (cG_mul_cG hc hd) (dG_pow_three hc hd) w b] at e
  exact Fin.ext e

omit hc hd in
theorem s1_lt : S1.all (fun w => w.all fun j => decide (j < 6)) = true := by decide +kernel

theorem orbit0_le : 66825 ≤ (orbit Ly0.B0 p0).ncard := by
  have hL : ∀ w ∈ ([[0], [1], [2], [3], [4], [5]] : List (List Nat)), ∀ j ∈ w, j < 6 := by
    decide
  exact orbitOK_sound Ly0.B0 (nets_valid hL) (nets_act hc hd hL Ly0.B0 fun w _ => wG_wZ_mem w)
    p0 orb0_ok

theorem orbit1_le :
    20160 ≤ (orbit ↥(Ly0.B0 ⊓ stabilizer (Perm (Fin Ly0.deg)) p0) p3).ncard := by
  have hL : ∀ w ∈ S1, ∀ j ∈ w, j < 6 := fun w hw j hj =>
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 s1_lt w hw) j hj)
  refine orbitOK_sound _ (nets_valid hL) (nets_act hc hd hL _ fun w hw =>
    Subgroup.mem_inf.2 ⟨wG_wZ_mem w, mem_stabilizer_iff.2 ?_⟩) p3 orb1_ok
  exact wG_fix hc hd (List.all_eq_true.1 s1_fix w hw) p0 List.mem_cons_self

theorem orbit2_le :
    4 ≤ (orbit ↥(Ly0.B0 ⊓ stabilizer (Perm (Fin Ly0.deg)) p0 ⊓
      stabilizer (Perm (Fin Ly0.deg)) p3) p1).ncard := by
  refine treeOK_orbit _ (fun g => ?_) tree2_ok
  have hfix : fixAll cL dL [0, 3] (S2.getD g []) = true := by
    rw [List.getD_eq_getElem?_getD]
    cases h : S2[g]? with
    | none => rfl
    | some w => exact List.all_eq_true.1 s2_fix w (List.mem_of_getElem? h)
  refine ⟨Ly0.wG Ly0.gens0 (wZ (S2.getD g [])),
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨wG_wZ_mem _,
      mem_stabilizer_iff.2 (wG_fix hc hd hfix p0 (by simp))⟩,
      mem_stabilizer_iff.2 (wG_fix hc hd hfix p3 (by simp))⟩,
    fun a => jwPt_wG hc hd (cG_mul_cG hc hd) (dG_pow_three hc hd) _ a⟩

theorem eq_one_of_fix_base (hbc : RB5Bound) {g : Perm (Fin Ly0.deg)} (hg : g ∈ Ly0.B0)
    (h0 : g p0 = p0) (h3 : g p3 = p3) (h1 : g p1 = p1) : g = 1 :=
  eq_one_of_fix3 Ly0.B0 p0 p3 p1 (m₀ := 66825) (m₁ := 20160) (m₂ := 4) (by norm_num)
    ((card_B0_le hc hd hbc).trans (by norm_num)) (orbit0_le hc hd) (orbit1_le hc hd)
    (orbit2_le hc hd) hg h0 h3 h1

theorem lift_gBs_of_wB (hbc : RB5Bound) {r : List (Fin 6 × Bool)} (h : wB r = true) :
    FreeGroup.lift gBs (FreeGroup.mk r) = 1 := by
  obtain ⟨hb, hfix⟩ := bFix_sound (cF := cL) (dF := dL) (bs := base) h
  have hf : fixAll cL dL base (r.map letIdx) = true := (andB_true h).2
  apply Subtype.ext
  rw [coe_lift_gBs, lift_gB_eq_wG hc hd hb]
  exact eq_one_of_fix_base hc hd hbc (wG_wZ_mem _) (wG_fix hc hd hf p0 (by decide))
    (wG_fix hc hd hf p3 (by decide)) (wG_fix hc hd hf p1 (by decide))

end Letters

theorem fam_fix_all : (Rcore107 ++ modularLearned).all (fun r => !isBWord r || wB r) = true := by
  refine all_of_chunks _ 16 11 _ (by decide +kernel) fun j hj => ?_
  interval_cases j
  exacts [bfam0, bfam1, bfam2, bfam3, bfam4, bfam5, bfam6, bfam7, bfam8, bfam9, bfam10]

theorem steps_fix_all : ∀ i < 11, (stepsAt i).all stepFix = true := by
  intro i hi
  interval_cases i
  · refine all_of_chunks _ 40 4 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exacts [b0_0, b0_1, b0_2, b0_3]
  · refine all_of_chunks _ 40 4 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exacts [b1_0, b1_1, b1_2, b1_3]
  · refine all_of_chunks _ 40 1 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exact b2_0
  · refine all_of_chunks _ 40 2 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exacts [b3_0, b3_1]
  · refine all_of_chunks _ 40 5 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exacts [b4_0, b4_1, b4_2, b4_3, b4_4]
  · refine all_of_chunks _ 40 2 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exacts [b5_0, b5_1]
  · refine all_of_chunks _ 40 5 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exacts [b6_0, b6_1, b6_2, b6_3, b6_4]
  · refine all_of_chunks _ 40 2 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exacts [b7_0, b7_1]
  · refine all_of_chunks _ 40 1 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exact b8_0
  · refine all_of_chunks _ 40 10 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exacts [b9_0, b9_1, b9_2, b9_3, b9_4, b9_5, b9_6, b9_7, b9_8, b9_9]
  · refine all_of_chunks _ 40 8 _ (by decide +kernel) fun j hj => ?_
    interval_cases j
    exacts [b10_0, b10_1, b10_2, b10_3, b10_4, b10_5, b10_6, b10_7]

theorem dist2_word_fix : ∀ r ∈ dist2BWords, wB r = true := by
  intro r hr
  unfold dist2BWords at hr
  rw [List.mem_eraseDups, List.mem_append] at hr
  rcases hr with hr | hr
  · exact List.all_eq_true.1 inv_fix r hr
  · obtain ⟨d, hd, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨s, hs, hsr⟩ := List.mem_filterMap.1 hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    have hlen : dist2Derivs.length = 11 := by decide +kernel
    have hs' : s ∈ stepsAt i := by
      unfold stepsAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact hs
    have h := List.all_eq_true.1 (steps_fix_all i (by omega)) s hs'
    rcases s with ⟨pos, kind, old, new⟩
    cases kind
    · have e : parseWord old ++ derivInv (parseWord new) = r := Option.some.inj hsr
      rw [← e]
      exact h
    all_goals simp at hsr

theorem dist2BWords_eq_one (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound) :
    ∀ r ∈ dist2BWords, isBWord r = true ∧ FreeGroup.lift gBs (FreeGroup.mk r) = 1 := by
  intro r hr
  have h := dist2_word_fix r hr
  exact ⟨(andB_true h).1, lift_gBs_of_wB hc hd hbc h⟩

theorem rfam_bword_eq_one (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound) :
    ∀ r ∈ Rcore107 ++ modularLearned ++ dist2BWords, isBWord r = true →
      FreeGroup.lift gBs (FreeGroup.mk r) = 1 := by
  intro r hr hb
  rcases List.mem_append.1 hr with hr | hr
  · have h := List.all_eq_true.1 fam_fix_all r hr
    rw [hb, Bool.not_true, Bool.false_or] at h
    exact lift_gBs_of_wB hc hd hbc h
  · exact (dist2BWords_eq_one hc hd hbc r hr).2

end CertificateChecks.KernelLyBase

end
