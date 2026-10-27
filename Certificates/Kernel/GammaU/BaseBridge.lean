
module

public import Certificates.Kernel.GammaU.CensusCfg
public import Certificates.Kernel.GammaU.Frame
public import Certificates.Kernel.GammaU.ColPt
public import Certificates.Kernel.GammaU.S0Bridge
public import CFSG.GF2Type.Smith1979.GammaU.CensusDefs
public import CFSG.GF2Type.Smith1979.GammaU.FrameLemma

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUBB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS CFSG.KD.IF4L CFSG.KD.GUF
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem compFacts : CompFacts := fun c hc g hg => by
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
  have hl5 : l < 5 := by rw [← CFSG.KD.GUCB.length_compGens c]; exact hl
  have h := compGens_mem hc hl5
  rwa [List.getD_eq_getElem _ _ hl] at h

theorem mem_foldl_sp (gens : List (Array ℕ)) :
    ∀ acc : List (Array ℕ), ∀ x ∈ acc,
      x ∈ gens.foldl (fun acc g => acc ++ acc.map (mulR g)) acc := by
  induction gens with
  | nil => exact fun acc x hx => hx
  | cons g gs ih => exact fun acc x hx => ih _ x (List.mem_append_left _ hx)

theorem gen_mem_sp {gens : List (Array ℕ)} {g : Array ℕ} (hg : g ∈ gens) :
    mulR g idR ∈ subsetProducts gens := by
  unfold subsetProducts
  suffices h : ∀ (gens : List (Array ℕ)) (acc : List (Array ℕ)), idR ∈ acc → g ∈ gens →
      mulR g idR ∈ gens.foldl (fun acc g => acc ++ acc.map (mulR g)) acc from
    h gens [idR] (List.mem_singleton_self _) hg
  intro gens
  induction gens with
  | nil => exact fun _ _ hg => by simp at hg
  | cons g' gs ih =>
    intro acc hacc hg
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hg with rfl | hg
    · exact mem_foldl_sp gs _ _ (List.mem_append_right _ (List.mem_map.2 ⟨idR, hacc, rfl⟩))
    · exact ih _ (List.mem_append_left _ hacc) hg

theorem rowsSet_gen {c : Nat} {r : Array ℕ} (hr : r ∈ ResPair.compGens c) {g : GL}
    (hg : ∀ x, g x = linOfRows r x) : RowsSet (compOf c) g :=
  ⟨mulR r idR, gen_mem_sp hr, fun x => by rw [hg, linOfRows_mulR, linOfRows_idR]⟩

theorem mem_pGrp_of_rows {c : Nat} (hc : c < 32) {u : GL} (hu : RowsSet (compOf c) u) :
    u ∈ pGrp (five CFSG.KD.GUC0.CG c) := by
  rw [CFSG.KD.GUCB.pGrp_eq_genGrp hc]
  obtain ⟨r, hr, hur⟩ := hu
  obtain ⟨l, hl, hlr⟩ := subsetProducts_mem (L := Viol.genGrp (ResPair.compGens c))
    (fun g hg => by
      obtain ⟨U, -, hU⟩ := compFacts c hc g hg
      exact ⟨U, Subgroup.subset_closure ⟨g, hg, hU⟩, hU⟩) r hr
  have : u = l := LinearEquiv.ext fun x => by rw [hur, hlr]
  rw [this]
  exact hl

theorem le_eq {c : Nat} (hc : c < 32) {T : GL} {Le : Subgroup GL}
    (hLe : ∀ l, l ∈ Le ↔ ∃ r ∈ compOf c, ∀ x, (T⁻¹ * l * T) x = linOfRows r x) :
    Le = (pGrp (five CFSG.KD.GUC0.CG c)).map (MulAut.conj T).toMonoidHom := by
  apply le_antisymm
  · intro l hl
    refine Subgroup.mem_map.2 ⟨T⁻¹ * l * T, mem_pGrp_of_rows hc ((hLe l).1 hl), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [Subgroup.map_le_iff_le_comap, CFSG.KD.GUCB.pGrp_eq_genGrp hc, Viol.genGrp,
      Subgroup.closure_le]
    rintro g ⟨r, hr, hgr⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine (hLe _).2 ?_
    obtain ⟨x, hx, hxg⟩ := rowsSet_gen hr hgr
    refine ⟨x, hx, fun y => ?_⟩
    rw [← hxg]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, LinearEquiv.mul_apply,
      inv_apply_apply]

theorem θA_eq : CFSG.KD.GUC0.θA = thetaU :=
  LinearEquiv.ext fun v => by rw [CFSG.KD.GUC0.isP_θA v, CFSG.KD.GUTB.linP_TH, thetaU_apply]

theorem candGrp_eq {i : Nat} (hi : i < 32) (Le : Subgroup GL) :
    candGrp i Le = candR (pGrp (five CFSG.KD.GUC0.CG i)) Le CFSG.KD.GUC0.θA := by
  rw [θA_eq, candGrp, candR]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro l ((hl | hl) | hl)
    · exact Subgroup.subset_closure (Or.inl (Or.inl (mem_pGrp_of_rows hi hl)))
    · exact Subgroup.subset_closure (Or.inl (Or.inr hl))
    · exact Subgroup.subset_closure (Or.inr hl)
  · rw [Subgroup.closure_le]
    rintro l ((hl | hl) | hl)
    · have hl' : l ∈ Viol.genGrp (ResPair.compGens i) := by
        rw [← CFSG.KD.GUCB.pGrp_eq_genGrp hi]
        exact hl
      refine (Subgroup.closure_le _).2 ?_ hl'
      rintro g ⟨r, hr, hgr⟩
      exact Subgroup.subset_closure (Or.inl (Or.inl (rowsSet_gen hr hgr)))
    · exact Subgroup.subset_closure (Or.inl (Or.inr hl))
    · exact Subgroup.subset_closure (Or.inr hl)

@[expose] noncomputable def TD (j : Nat) : GL := autP (look CFSG.KD.GUCC.DT j)

theorem isP_TD {j : Nat} (hj : j < 108) : IsP (TD j) (look CFSG.KD.GUCC.DT j) :=
  isP_autP (IsP.exists_of_mul (CFSG.KD.GUCC.inv_spec.2 j hj))

theorem ch16966bb_dt0 : look CFSG.KD.GUCC.DT 0 = idP := by decide +kernel

theorem TD_zero : TD 0 = 1 := IsP.inj (isP_TD (by norm_num)) (by rw [ch16966bb_dt0]; exact IsP.one)

theorem frameTr : FrameTr TD 108 := by
  refine ⟨fun j hj => dt_mem hj (isP_TD hj), ⟨0, by norm_num, ?_⟩, fun r hr j hj => ?_⟩
  · rw [TD_zero]
    ext y
    simp
  · obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hr
    have hs2 : s < 2 := by
      rw [show saGens.length = 2 from rfl] at hs
      exact hs
    obtain ⟨j', hj', hperm⟩ := sa_perm hs2 hj
    obtain ⟨U, hU⟩ := IsP.exists_of_mul (sa_lists.2 s hs2)
    obtain ⟨hSA, hrows⟩ := cf16966_sap
    rw [hSA, nthD_map _ _ _ #[] hs] at hU
    have hmem : saGens.getD s #[] ∈ saGens := by
      rw [getD_of_lt _ hs]
      exact List.getElem_mem hs
    have hUr := (isP_packR (List.all_eq_true.1 hrows _ hmem) U).1 hU
    rw [getD_of_lt _ hs] at hUr
    refine ⟨j', hj', ?_⟩
    have hcomp : (linOfRows saGens[s]).comp (TD j : V12 →ₗ[ZMod 2] V12) =
        ((U * TD j : GL) : V12 →ₗ[ZMod 2] V12) :=
      LinearMap.ext fun y => (hUr _).symm
    rw [← Submodule.map_comp]
    refine (congrArg (fun f => Submodule.map f (spanOf d0)) hcomp).trans
      (hperm U (TD j) (TD j') (fun y => ?_) (isP_TD hj) (isP_TD hj'))
    rw [getD_of_lt _ hs]
    exact hUr y

@[expose] noncomputable def te0 (e : Nat) : GL :=
  open Classical in
  if h : ∃ n, n < CFSG.KD.GUCC.NE ∧ ap12 (look CFSG.KD.GUCC.TE n) 3072 = e then
    autP (look CFSG.KD.GUCC.TE h.choose) else 1

theorem ch16966bb_ne : CFSG.KD.GUCC.NE = 4 := by decide +kernel

theorem te0_spec {e : Nat} (he : ∃ n < CFSG.KD.GUCC.NE, ap12 (look CFSG.KD.GUCC.TE n) 3072 = e) :
    ∃ n < 4, IsP (te0 e) (look CFSG.KD.GUCC.TE n) ∧ ap12 (look CFSG.KD.GUCC.TE n) 3072 = e := by
  classical
  have he' : ∃ n, n < CFSG.KD.GUCC.NE ∧ ap12 (look CFSG.KD.GUCC.TE n) 3072 = e := by
    obtain ⟨n, hn, h⟩ := he
    exact ⟨n, hn, h⟩
  have hn := he'.choose_spec
  have hn4 : he'.choose < 4 := lt_of_lt_of_eq hn.1 ch16966bb_ne
  refine ⟨he'.choose, hn4, ?_, hn.2⟩
  rw [te0, dif_pos he']
  exact isP_autP (IsP.exists_of_mul (CFSG.KD.GUCC.inv_spec.1 _ hn4))

theorem colTr_of {r0 : Array ℕ}
    (hcol : ∀ e, e ∈ colPts r0 ↔ ∃ n < CFSG.KD.GUCC.NE, ap12 (look CFSG.KD.GUCC.TE n) 3072 = e) :
    ColTr te0 r0 := by
  intro e he
  obtain ⟨n, hn, hT, hne⟩ := te0_spec ((hcol e).1 he)
  refine ⟨te_mem (by rw [ch16966bb_ne]; exact hn) hT, ?_⟩
  rw [hT, ← hne, vecOf_ap12]
  rfl

theorem colTr0 : ColTr te0 (rowsP CFSG.KD.GUC0.S0) := colTr_of CFSG.KD.GUCP.colPts_s0_0

theorem colTr1 : ColTr te0 (rowsP CFSG.KD.GUC1.S0) := colTr_of CFSG.KD.GUCP.colPts_s0_1

theorem cfg_data {r0 : Array ℕ}
    (hcol : ∀ e, e ∈ colPts r0 ↔ ∃ n < CFSG.KD.GUCC.NE, ap12 (look CFSG.KD.GUCC.TE n) 3072 = e)
    {e j : Nat} (he : e ∈ colPts r0) (hj : j < 108) :
    ∃ n < 4, IsP (te0 e * TD j) (mulP (look CFSG.KD.GUCC.TE n) (look CFSG.KD.GUCC.DT j)) ∧
      (vecOf a0 ∈ (spanOf d0).map ((te0 e * TD j : GL) : V12 →ₗ[ZMod 2] V12) →
        ap12 (mulP (look CFSG.KD.GUCC.DTi j) (look CFSG.KD.GUCC.TEi n)) 3072 ∈ spanList d0) := by
  obtain ⟨n, hn, hT, -⟩ := te0_spec ((hcol e).1 he)
  have hTT := hT.mul (isP_TD hj)
  refine ⟨n, hn, hTT, fun ha => ?_⟩
  have hTi := CFSG.KD.GUCC.isP_T hn hj hTT
  obtain ⟨z, hz, hza⟩ := Submodule.mem_map.1 ha
  rw [mem_spanList_iff d0_lt (ap12_lt _ _), vecOf_ap12, ← hTi]
  change (te0 e * TD j)⁻¹ (vecOf a0) ∈ spanOf d0
  have : z = (te0 e * TD j)⁻¹ (vecOf a0) := by
    rw [← hza]
    exact (inv_apply_apply _ _).symm
  rw [← this]
  exact hz

theorem cfgAll0 {P : Subgroup GL → Prop}
    (hP : ∀ X < 384, fld CFSG.KD.GUC0.LB X = CFSG.KD.GUC0.AR →
      P (confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX CFSG.KD.GUC0.θA X)) :
    CfgAll 0 (rowsP CFSG.KD.GUC0.S0) TD 108 te0 P := by
  intro e he j hj c hc Le hLe ha hs hcard
  obtain ⟨n, hn, hT, ha'⟩ := cfg_data CFSG.KD.GUCP.colPts_s0_0 he hj
  obtain ⟨l, hl, hlr⟩ := hs
  have hlS : IsP l CFSG.KD.GUC0.S0 := fun v => hlr v
  have hs' := mem_pGrp_of_rows hc ((hLe l).1 hl)
  obtain ⟨X, hX, hFT, hFC⟩ := CFSG.KD.GUC0.cfg_complete hn hj hc hT hlS (ha' ha) hs'
  have hTX : CFSG.KD.GUC0.TX X = te0 e * TD j :=
    IsP.inj (CFSG.KD.GUC0.isP_TX hX) (by rw [hFT]; exact hT)
  have hR : candGrp 0 Le = confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX
      CFSG.KD.GUC0.θA X := by
    rw [candGrp_eq (by norm_num), le_eq hc hLe, confR, hFC, hTX]
  rw [hR] at hcard ⊢
  exact hP X hX ((CFSG.KD.GUC0.census_s0 X hX).1.1 hcard)

theorem cfgAll1 {P : Subgroup GL → Prop}
    (hP : ∀ X < 384, fld CFSG.KD.GUC1.LB X = CFSG.KD.GUC1.AR →
      P (confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX CFSG.KD.GUC1.θA X)) :
    CfgAll 1 (rowsP CFSG.KD.GUC1.S0) TD 108 te0 P := by
  intro e he j hj c hc Le hLe ha hs hcard
  obtain ⟨n, hn, hT, ha'⟩ := cfg_data CFSG.KD.GUCP.colPts_s0_1 he hj
  obtain ⟨l, hl, hlr⟩ := hs
  have hlS : IsP l CFSG.KD.GUC1.S0 := fun v => hlr v
  have hs' := mem_pGrp_of_rows hc ((hLe l).1 hl)
  rw [← CFSG.KD.GUC1.cg_eq.1] at hs'
  obtain ⟨X, hX, hFT, hFC⟩ := CFSG.KD.GUC1.cfg_complete hn hj hc hT hlS (ha' ha) hs'
  have hTX : CFSG.KD.GUC1.TX X = te0 e * TD j :=
    IsP.inj (CFSG.KD.GUC1.isP_TX hX) (by rw [hFT]; exact hT)
  have hθ : CFSG.KD.GUC1.θA = CFSG.KD.GUC0.θA := by
    rw [CFSG.KD.GUC1.θA, CFSG.KD.GUC0.θA, CFSG.KD.GUC1.cg_eq.2]
  have hR : candGrp 1 Le = confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX
      CFSG.KD.GUC1.θA X := by
    rw [candGrp_eq (by norm_num), le_eq hc hLe, confR, hFC, hTX, hθ, CFSG.KD.GUC1.cg_eq.1]
  rw [hR] at hcard ⊢
  exact hP X hX ((CFSG.KD.GUC1.census_s0 X hX).1.1 hcard)

end CFSG.KD.GUBB

end
