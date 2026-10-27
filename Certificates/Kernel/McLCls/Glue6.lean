module

public import Certificates.Kernel.McLCls.Glue5

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLCls

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.M305
  CertificateChecks.KernelLC.McLC CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Quasithin.KGC31
  CFSG.SectionRank.QTK.Insp443.McLCls CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore.Native CFSG.KS.MulH

theorem card_O : F.O.card = 7 := by
  decide +kernel

@[expose] def σ1 : Equiv.Perm (Fin 7) :=
  ⟨![1, 4, 6, 2, 3, 0, 5], ![5, 0, 3, 4, 1, 6, 2], by decide, by decide⟩

@[expose] def σ2 : Equiv.Perm (Fin 7) :=
  ⟨![6, 5, 1, 2, 0, 4, 3], ![4, 2, 3, 6, 5, 1, 0], by decide, by decide⟩

theorem prep_AE : ∀ k < AE.ng, PRep 7 4 (AE.G k) ([σ1, σ2].getD k 1) := by
  intro k hk
  have hk2 : k < 2 := hk
  interval_cases k
  · unfold PRep
    decide +kernel
  · unfold PRep
    decide +kernel

theorem card_K0 : Nat.card (closure {s | s ∈ [σ1, σ2]}) = 2520 := by
  rw [(CFSG.ClassicalInvolution.ListBridge.enum_closure AE.ok rfl prep_AE).2]
  rfl

@[expose] def oSf : Fin 7 → Fin 275 := ![0, 26, 208, 213, 227, 260, 270]

theorem oSf_mem (i : Fin 7) : oSf i ∈ F.O := by
  rw [← mem_oS_iff]
  fin_cases i <;> decide

@[expose] def ιO (i : Fin 7) : {x // x ∈ F.O} := ⟨oSf i, oSf_mem i⟩

theorem ιO_inj : Function.Injective ιO := by
  intro a b h
  have h1 : oSf a = oSf b := congrArg Subtype.val h
  revert h1
  revert a b
  decide

theorem ιO_bij : Function.Bijective ιO :=
  (Fintype.bijective_iff_injective_and_card ιO).2 ⟨ιO_inj, by
    rw [Fintype.card_fin, Fintype.card_coe, card_O]⟩


@[expose] noncomputable def τ : Equiv.Perm (Fin 7) :=
  (Equiv.ofBijective ιO ιO_bij).trans (F.O.equivFinOfCardEq card_O)

@[expose] noncomputable def rho : ↥F.M →* Equiv.Perm (Fin 7) :=
  (setAct F.O card_O).comp (Subgroup.inclusion M_le_setStab)

theorem rho_eq_one_iff (x : ↥F.M) :
    rho x = 1 ↔ ∀ i ∈ F.O, (x : Equiv.Perm (Fin 275)) i = i :=
  setAct_eq_one_iff F.O card_O (Subgroup.inclusion M_le_setStab x)

theorem rho_eq {m : ↥F.M} {σ : Equiv.Perm (Fin 7)}
    (h : ∀ i : Fin 7, (m : Equiv.Perm (Fin 275)) (oSf i) = oSf (σ i)) :
    rho m = τ * σ * τ⁻¹ := by
  refine Equiv.ext fun j => ?_
  set e := F.O.equivFinOfCardEq card_O
  set ι := Equiv.ofBijective ιO ιO_bij
  obtain ⟨k, hk⟩ : ∃ k, ι k = e.symm j := ι.surjective _
  have hj : j = e (ι k) := by rw [hk, Equiv.apply_symm_apply]
  have hτ : ∀ i, τ i = e (ι i) := fun i => rfl
  have hτk : τ⁻¹ j = k := by
    rw [Equiv.Perm.inv_eq_iff_eq, hτ, hj]
  have key : rho m (e (ι k)) = e (ι (σ k)) := by
    simp only [rho, MonoidHom.comp_apply, setAct, MonoidHom.coe_mk, OneHom.coe_mk,
      Equiv.permCongr_apply, Equiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    have e1 : (F.O.equivFinOfCardEq card_O).symm (e (ι k)) = ι k := e.symm_apply_apply _
    rw [e1]
    exact h k
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτk, hτ, hj, key]

theorem m1_act (i : Fin 7) : tp 275 (clsTbl 4) (oSf i) = oSf (σ1 i) := by
  have h : ∀ i : Fin 7, pg 9 (mask 9) (CT.F 4) (oSf i) = (oSf (σ1 i) : ℕ) := by
    decide +kernel
  exact Fin.ext ((prep_cls (k := 4) (by norm_num) (oSf i)).symm.trans (h i))

theorem m2_act (i : Fin 7) : tp 275 (clsTbl 5) (oSf i) = oSf (σ2 i) := by
  have h : ∀ i : Fin 7, pg 9 (mask 9) (CT.F 5) (oSf i) = (oSf (σ2 i) : ℕ) := by
    decide +kernel
  exact Fin.ext ((prep_cls (k := 5) (by norm_num) (oSf i)).symm.trans (h i))

@[expose] noncomputable def mE (j : Nat) : ↥F.M := ⟨gM j, gM_mem j⟩

theorem rho_m1 : rho (mE 0) = τ * σ1 * τ⁻¹ := rho_eq m1_act

theorem rho_m2 : rho (mE 1) = τ * σ2 * τ⁻¹ := rho_eq m2_act

theorem card_range_ge : 2520 ≤ Nat.card rho.range := by
  have hK : (closure {s | s ∈ [σ1, σ2]}).map (MulAut.conj τ).toMonoidHom ≤ rho.range := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨s, hs, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hs
    rcases hs with rfl | rfl
    · exact ⟨mE 0, by rw [rho_m1]; rfl⟩
    · exact ⟨mE 1, by rw [rho_m2]; rfl⟩
  have h := Subgroup.card_le_of_le hK
  rwa [Subgroup.card_map_of_injective (MulAut.conj τ).injective, card_K0] at h

theorem W_le_ker : F.W.subgroupOf F.M ≤ rho.ker := fun x hx =>
  (rho_eq_one_iff x).2 fun i hi => W_fix _ (Subgroup.mem_subgroupOf.mp hx) i hi

theorem card_Wsub : Nat.card (F.W.subgroupOf F.M) = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe W_le_M).toEquiv, card_W]

theorem card_M_eq : Nat.card F.M = Nat.card rho.range * Nat.card rho.ker := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange rho).toEquiv]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup rho.ker

theorem M_le_N : F.M ≤ mclP ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275))) :=
  le_inf M_le_P M_le_norm

theorem card_M : Nat.card F.M = 40320 ∧ Nat.card rho.range = 2520 ∧
    rho.ker = F.W.subgroupOf F.M := by
  have hup : Nat.card F.M ≤ 40320 := (Subgroup.card_le_of_le M_le_N).trans card_normP
  have hk : 16 ≤ Nat.card rho.ker := card_Wsub ▸ Subgroup.card_le_of_le W_le_ker
  have hr := card_range_ge
  have he := card_M_eq
  have hr' : Nat.card rho.range = 2520 := by nlinarith
  have hk' : Nat.card rho.ker = 16 := by nlinarith
  refine ⟨by nlinarith, hr', ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge W_le_ker (by rw [hk', card_Wsub])).symm

theorem ker_fact : ∀ g ∈ F.M, (∀ i ∈ F.O, g i = i) → g ∈ F.W := by
  intro g hg h
  have h1 : (⟨g, hg⟩ : ↥F.M) ∈ rho.ker := (rho_eq_one_iff _).2 h
  rw [card_M.2.2] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem M_eq_N : F.M = mclP ⊓ normalizer (F.W : Set (Equiv.Perm (Fin 275))) :=
  Subgroup.eq_of_le_of_card_ge M_le_N (by rw [card_M.1]; exact card_normP)

theorem range_rho : rho.range = alternatingGroup (Fin 7) :=
  CFSG.Quasithin.KGC31.A7.eq_alt7_of_card card_M.2.1

theorem cent_fact : ∀ g ∈ mclP, (∀ w ∈ F.W, g * w = w * g) → g ∈ F.W := by
  intro g hgP hgc
  have hgN : g ∈ normalizer (F.W : Set (Equiv.Perm (Fin 275))) := by
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have e : g * w * g⁻¹ = w := by rw [hgc w hw, mul_inv_cancel_right]
      rw [e]
      exact hw
    · intro hw
      have e : g * (g * w * g⁻¹) = (g * w * g⁻¹) * g := hgc _ hw
      have ew : w = g * w * g⁻¹ := by
        calc w = g⁻¹ * ((g * w * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * w * g⁻¹)) := by rw [e]
          _ = g * w * g⁻¹ := by group
      rw [ew]
      exact hw
  have hgM : g ∈ F.M := by
    rw [M_eq_N]
    exact Subgroup.mem_inf.mpr ⟨hgP, hgN⟩
  let Cs : Subgroup ↥F.M := (centralizer (F.W : Set (Equiv.Perm (Fin 275)))).subgroupOf F.M
  have hCs : Cs.Normal := by
    constructor
    intro n hn x
    rw [Subgroup.mem_subgroupOf, mem_centralizer_iff] at hn ⊢
    intro w hw
    have hx : (x : Equiv.Perm (Fin 275)) ∈ normalizer (F.W : Set (Equiv.Perm (Fin 275))) :=
      M_le_norm x.2
    have hw' : (x : Equiv.Perm (Fin 275))⁻¹ * w * (x : Equiv.Perm (Fin 275))⁻¹⁻¹ ∈ F.W :=
      (mem_normalizer_iff.mp ((normalizer (F.W : Set (Equiv.Perm (Fin 275)))).inv_mem hx) w).mp hw
    rw [inv_inv] at hw'
    have hc := hn _ hw'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc w * (↑x * ↑n * (↑x)⁻¹) = ↑x * ((↑x)⁻¹ * w * ↑x * ↑n) * (↑x)⁻¹ := by group
      _ = ↑x * (↑n * ((↑x)⁻¹ * w * ↑x)) * (↑x)⁻¹ := by rw [hc]
      _ = ↑x * ↑n * (↑x)⁻¹ * w := by group
  let rhoA : ↥F.M →* ↥(alternatingGroup (Fin 7)) :=
    rho.codRestrict _ fun x => by rw [← range_rho]; exact ⟨x, rfl⟩
  have hsurj : Function.Surjective rhoA := by
    intro σ
    have hσ : (σ : Equiv.Perm (Fin 7)) ∈ rho.range := by rw [range_rho]; exact σ.2
    obtain ⟨x, hx⟩ := hσ
    exact ⟨x, Subtype.ext hx⟩
  have hN' := hCs.map rhoA hsurj
  have := CFSG.Quasithin.KGC31.A7.alt7_simple
  have hgCs : (⟨g, hgM⟩ : ↥F.M) ∈ Cs := by
    rw [Subgroup.mem_subgroupOf, mem_centralizer_iff]
    intro w hw
    exact (hgc w hw).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Cs.map rhoA) with h | h
  · have h1 : rhoA ⟨g, hgM⟩ = 1 := by
      have : rhoA ⟨g, hgM⟩ ∈ Cs.map rhoA := ⟨_, hgCs, rfl⟩
      rw [h] at this
      exact this
    have h2 : (⟨g, hgM⟩ : ↥F.M) ∈ rho.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
    rw [card_M.2.2] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  · exfalso
    have h1 : rhoA (mE 0) ∈ Cs.map rhoA := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hce⟩ := h1
    have h2 : c⁻¹ * mE 0 ∈ rho.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have e : rho c = rho (mE 0) := congrArg Subtype.val hce
      rw [e, inv_mul_cancel]
    rw [card_M.2.2, Subgroup.mem_subgroupOf] at h2
    have hcC := Subgroup.mem_subgroupOf.mp hc
    rw [mem_centralizer_iff] at hcC
    set w := ((c⁻¹ * mE 0 : ↥F.M) : Equiv.Perm (Fin 275))
    have hm : gM 0 = (c : Equiv.Perm (Fin 275)) * w := by
      change gM 0 = (c : Equiv.Perm (Fin 275)) * ((c : Equiv.Perm (Fin 275))⁻¹ * gM 0)
      group
    have hwt : w * F.t0 = F.t0 * w := by
      rw [W_eq] at h2
      exact eSub_comm basis_fact _ _ h2 (W_eq ▸ t0_mem_W)
    have hct : F.t0 * c = c * F.t0 := hcC _ t0_mem_W
    have hcomm : gM 0 * F.t0 = F.t0 * gM 0 := by
      rw [hm]
      calc (c : Equiv.Perm (Fin 275)) * w * F.t0 = c * (w * F.t0) := by group
        _ = c * (F.t0 * w) := by rw [hwt]
        _ = (c * F.t0) * w := by group
        _ = (F.t0 * c) * w := by rw [hct]
        _ = F.t0 * (c * w) := by group
    exact ne_of_beq (canon_mul (canon_cls (k := 4) (by norm_num)) canon_cen4)
      (canon_mul canon_cen4 (canon_cls (k := 4) (by norm_num)))
      (prep_mul (prep_cls (k := 4) (by norm_num)) prep_cen4)
      (prep_mul prep_cen4 (prep_cls (k := 4) (by norm_num))) nrm_parts.2.2 hcomm

theorem facts : CFSG.SectionRank.QTK.Insp443.McLCls.Facts where
  tbls := tbls_fact
  basis := basis_fact
  mOne := ⟨W_le_M, M_le_norm, card_M.1, M_le_setStab, W_fix, ker_fact⟩
  cent := ⟨cent_fact, card_normH⟩
  sTwo := sTwo_fact
  cls := cls_fact
  e8 := e8_fact

end CertificateChecks.KernelMcLCls

end
