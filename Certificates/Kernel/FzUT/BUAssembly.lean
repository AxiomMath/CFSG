module

public import Certificates.Kernel.FzUT.BUCheck
public import Certificates.Kernel.FzUT.Norm
public import CFSG.Certificates.Kernel.FzUT.BUCond

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII CFSG.GH74.GLS.Bg.TwoGroups

theorem fzbu_repFacts : allB 2 (fun c => allB 64 (fun x =>
    andB (Nat.beq (cfP (repSY c 0) (repSY c 1) (cfP (repSY c 0) (repSY c 1) x)) x)
      (Nat.beq (cfP (repSY c 0) (repSY c 1) (cfP 4 17 x))
        (cfP 4 17 (cfP 4 17 (cfP 4 17 (cfP (repSY c 0) (repSY c 1) x))))))) = true := by
  decide +kernel

theorem fzbRepD_q : ∀ c : Bool,
    (⟨dec 4, dec (rhoBP 4), dec 17, dec (rhoBP 17)⟩ : FzAutD) = fzbRepD c 0 := by
  decide +kernel

theorem fzbRepD_s : ∀ c : Fin 2,
    (⟨dec (repSY c 0), dec (rhoBP (repSY c 0)), dec (repSY c 1), dec (rhoBP (repSY c 1))⟩ :
      FzAutD) = fzbRepD (decide ((c : ℕ) = 1)) 1 := by
  decide +kernel

theorem fzbRepD_y : ∀ c : Fin 2,
    (⟨dec (repSY c 2), dec (rhoBP (rhoBP (repSY c 2))), dec (repSY c 3),
      dec (rhoBP (rhoBP (repSY c 3)))⟩ : FzAutD) = fzbRepD (decide ((c : ℕ) = 1)) 2 := by
  decide +kernel

theorem gens_of_comm {B : MulAut FzUT} (hB : ∀ x, B (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (B x)))
    {p q : ℕ} (hp : enc (B fzE1) = p) (hq : enc (B fzF1) = q) :
    fzGens B = ⟨dec p, dec (rhoBP p), dec q, dec (rhoBP q)⟩ := by
  have hp' : p < 64 := hp ▸ enc_lt _
  have hq' : q < 64 := hq ▸ enc_lt _
  have d : ∀ {y : FzUT} {n : ℕ}, n < 64 → enc y = n → y = dec n := fun hn e =>
    enc_injective (by rw [e, enc_dec_lt hn])
  refine FzAutD.ext (d hp' hp) ?_ (d hq' hq) ?_
  · change B fzEW = _
    rw [eW_eq, hB]
    exact d (rhoBP_lt hp') (by rw [← rhoBP_eq, hp])
  · change B fzFW = _
    rw [fW_eq, hB]
    exact d (rhoBP_lt hq') (by rw [← rhoBP_eq, hq])

theorem gens_of_inv {B : MulAut FzUT}
    (hB : ∀ x, B (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (fzRho0 (fzRho0 (B x)))))
    {p q : ℕ} (hp : enc (B fzE1) = p) (hq : enc (B fzF1) = q) :
    fzGens B = ⟨dec p, dec (rhoBP (rhoBP p)), dec q, dec (rhoBP (rhoBP q))⟩ := by
  have hp' : p < 64 := hp ▸ enc_lt _
  have hq' : q < 64 := hq ▸ enc_lt _
  have d : ∀ {y : FzUT} {n : ℕ}, n < 64 → enc y = n → y = dec n := fun hn e =>
    enc_injective (by rw [e, enc_dec_lt hn])
  refine FzAutD.ext (d hp' hp) ?_ (d hq' hq) ?_
  · change B fzEW = _
    rw [eW_eq, hB]
    exact d (rhoBP_lt (rhoBP_lt hp')) (by rw [← rhoBP_eq, ← rhoBP_eq, hp])
  · change B fzFW = _
    rw [fW_eq, hB]
    exact d (rhoBP_lt (rhoBP_lt hq')) (by rw [← rhoBP_eq, ← rhoBP_eq, hq])

theorem rec_aut {h1 h3 k1 k3 : ℕ} (h : buRecOK h1 h3 k1 k3 = true) (h1lt : h1 < 64)
    (h3lt : h3 < 64) (k1lt : k1 < 64) (k3lt : k3 < 64) :
    ∃ H : MulAut FzUT, (∀ x, enc (H x) = cfP h1 h3 (enc x)) ∧
      (∀ x, H (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (H x))) ∧
      H⁻¹ fzE1 = dec k1 ∧ H⁻¹ fzF1 = dec k3 := by
  simp only [buRecOK, andB_true, Nat.beq_eq] at h
  obtain ⟨ha, hk1, hk3⟩ := h
  obtain ⟨H, he, hr⟩ := exists_cfAut h1lt h3lt ha
  refine ⟨H, he, hr, ?_, ?_⟩
  · have : H (dec k1) = fzE1 := enc_injective (by rw [he, enc_dec_lt k1lt, hk1, enc_e1])
    rw [← this, inv_apply_self]
  · have : H (dec k3) = fzF1 := enc_injective (by rw [he, enc_dec_lt k3lt, hk3, enc_f1])
    rw [← this, inv_apply_self]

theorem conj_codes {H σ : MulAut FzUT} {h1 h3 k1 k3 : ℕ} {F : ℕ → ℕ} {r1 r3 : ℕ}
    (hH : ∀ x, enc (H x) = cfP h1 h3 (enc x)) (hk1 : H⁻¹ fzE1 = dec k1)
    (hk3 : H⁻¹ fzF1 = dec k3) (k1lt : k1 < 64) (k3lt : k3 < 64)
    (hF : ∀ x, enc (σ x) = F (enc x)) (h : buConjOK h1 h3 k1 k3 F r1 r3 = true) :
    enc ((H * σ * H⁻¹) fzE1) = r1 ∧ enc ((H * σ * H⁻¹) fzF1) = r3 := by
  simp only [buConjOK, andB_true, Nat.beq_eq] at h
  rw [conj_apply, conj_apply, hk1, hk3, hH, hH, hF, hF, enc_dec_lt k1lt, enc_dec_lt k3lt]
  exact h

theorem comm_conj' {H r : MulAut FzUT} (hH : ∀ x, H (r x) = fzRho0 (fzRho0 (H x))) :
    H * r * H⁻¹ = fzRho0 * fzRho0 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := H.surjective x
  change H (r (H⁻¹ (H y))) = fzRho0 (fzRho0 (H y))
  rw [inv_apply_self, hH]

theorem comm_conj {H : MulAut FzUT} (hH : ∀ x, H (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (H x))) :
    H * (fzRho0 * fzRho0) * H⁻¹ = fzRho0 * fzRho0 :=
  comm_conj' hH

theorem bool_rec_true {b : Bool} (h : Bool.rec (motive := fun _ => Bool) true false b = true) :
    b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem fzb_core {aq as ay : MulAut FzUT} (A : FzbAdm (fzRho0 * fzRho0) aq as ay) :
    ∃ (c : Bool) (g : MulAut FzUT), (∀ x, g (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (g x))) ∧
      fzGens (g * aq * g⁻¹) = fzbRepD c 0 ∧ fzGens (g * as * g⁻¹) = fzbRepD c 1 ∧
      fzGens (g * ay * g⁻¹) = fzbRepD c 2 ∧
      (∀ x, as (as x) = x) ∧ (∀ x, as (aq x) = aq (aq (aq (as x)))) := by
  have st1 := fzbu_stage1
  unfold stage1 at st1
  rw [allB_iff] at st1
  have st1' := (allB_iff _ _).mp (st1 _ (enc_lt (aq fzE1))) _ (enc_lt (aq fzF1))
  rw [impB_true] at st1'
  have pre : andB (isInvP (enc (aq fzE1))) (andB (isInvP (enc (aq fzF1)))
      (qOK (enc (aq fzE1)) (enc (aq fzF1)))) = true := by
    rw [andB_true, andB_true]
    exact ⟨isInvP_of aq e1_ne e1_sq, isInvP_of aq f1_ne f1_sq, qOK_of_adm A⟩
  have sz := sZ_codes A
  rcases orB_true.mp (st1' pre) with hL | hN
  swap
  · exfalso
    unfold noS at hN
    have h1 := (allB_iff _ _).mp hN _ sz.1.2
    have h2 := bool_rec_true ((allB_iff _ _).mp h1 _ sz.2.2)
    rw [← sz.1.1, ← sz.2.1, sOK_of_adm A] at h2
    exact absurd h2 (by decide)
  obtain ⟨e, he, hm⟩ := (anyL_iff _ _).mp hL
  rw [andB_true, Nat.beq_eq, Nat.beq_eq] at hm
  have hl1 := (allL_iff _ _).mp fzbu_l1 e he
  unfold l1OK at hl1
  rw [andB_true] at hl1
  obtain ⟨H1, hH1, hr1, hk1, hk3⟩ := rec_aut hl1.1 (fld_lt _ _) (fld_lt _ _) (fld_lt _ _)
    (fld_lt _ _)
  have hq := hq_of A
  rw [hm.1, hm.2] at hl1
  obtain ⟨c1, c3⟩ := conj_codes hH1 hk1 hk3 (fld_lt _ _) (fld_lt _ _) hq hl1.2
  have A2 := fzbAdm_conj A H1
  rw [comm_conj hr1] at A2
  set aq2 := H1 * aq * H1⁻¹ with haq2
  set as2 := H1 * as * H1⁻¹ with has2
  set ay2 := H1 * ay * H1⁻¹ with hay2
  have sz2 := sZ_codes A2
  have st2 := fzbu_stage2
  unfold stage2 at st2
  have st2' := (allB_iff _ _).mp ((allB_iff _ _).mp st2 _ sz2.1.2) _ sz2.2.2
  rw [impB_true, ← sz2.1.1, ← sz2.2.1] at st2'
  have hs2 := sOK_of_adm A2
  rw [c1, c3] at hs2
  have st2'' := (allB_iff _ _).mp (st2' hs2) _ (enc_lt (ay2 fzE1))
  rw [impB_true] at st2''
  have hq2 : ∀ x, enc (aq2 x) = cfP 4 17 (enc x) := fun x => by rw [hq_of A2 x, c1, c3]
  have hf1 : aq2 fzE1 = fzF1 := enc_injective (by rw [c1, enc_f1])
  have hc3 : enc (ay2 fzF1) = cfP 4 17 (enc (ay2 fzE1)) := by
    rw [← hf1, A2.y_q, hq2]
  have hy2 := yOK_of_adm A2 c1 c3
  rw [hc3] at hy2
  obtain ⟨e', he', hm'⟩ := (anyL_iff _ _).mp (st2'' hy2)
  simp only [andB_true, Nat.beq_eq] at hm'
  have hl2 := (allL_iff _ _).mp fzbu_l2 e' he'
  unfold l2OK at hl2
  simp only [andB_true, Nat.blt_eq] at hl2
  obtain ⟨hc, hrec, hcq, hcs, hcy⟩ := hl2
  obtain ⟨H2, hH2, hr2, hk1', hk3'⟩ := rec_aut hrec (fld_lt _ _) (fld_lt _ _) (fld_lt _ _)
    (fld_lt _ _)
  have q3 := conj_codes hH2 hk1' hk3' (fld_lt _ _) (fld_lt _ _) hq2 hcq
  rw [hm'.1, hm'.2.1] at hcs
  have s3 := conj_codes hH2 hk1' hk3' (fld_lt _ _) (fld_lt _ _) (hs_of A2) hcs
  rw [hm'.2.2.1, hm'.2.2.2, ← hc3] at hcy
  have y3 := conj_codes hH2 hk1' hk3' (fld_lt _ _) (fld_lt _ _) (hy_of A2) hcy
  have A3 := fzbAdm_conj A2 H2
  rw [comm_conj hr2] at A3
  have eq : H2 * H1 * aq * (H2 * H1)⁻¹ = H2 * aq2 * H2⁻¹ := by rw [haq2]; group
  have es : H2 * H1 * as * (H2 * H1)⁻¹ = H2 * as2 * H2⁻¹ := by rw [has2]; group
  have ey : H2 * H1 * ay * (H2 * H1)⁻¹ = H2 * ay2 * H2⁻¹ := by rw [hay2]; group
  have hS : ∀ x, enc ((H2 * H1 * as * (H2 * H1)⁻¹) x) =
      cfP (repSY (fld e' 4) 0) (repSY (fld e' 4) 1) (enc x) := fun x => by
    rw [es, hs_of A3 x, s3.1, s3.2]
  have hQ : ∀ x, enc ((H2 * H1 * aq * (H2 * H1)⁻¹) x) = cfP 4 17 (enc x) := fun x => by
    rw [eq, hq_of A3 x, q3.1, q3.2]
  have rf := (allB_iff _ _).mp fzbu_repFacts _ hc
  have cg : ∀ (σ : MulAut FzUT) y, (H2 * H1) (σ y) = (H2 * H1 * σ * (H2 * H1)⁻¹) ((H2 * H1) y) :=
    fun σ y => by rw [conj_apply, inv_apply_self]
  refine ⟨decide (fld e' 4 = 1), H2 * H1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change H2 (H1 (fzRho0 (fzRho0 x))) = fzRho0 (fzRho0 (H2 (H1 x)))
    rw [hr1, hr2]
  · rw [eq, gens_of_comm (fun x => A3.q_r x) q3.1 q3.2]
    exact fzbRepD_q _
  · rw [es, gens_of_comm (fun x => A3.s_r x) s3.1 s3.2]
    exact fzbRepD_s ⟨fld e' 4, hc⟩
  · rw [ey, gens_of_inv (fun x => A3.y_r x) y3.1 y3.2]
    exact fzbRepD_y ⟨fld e' 4, hc⟩
  · intro x
    have h := (allB_iff _ _).mp rf _ (enc_lt ((H2 * H1) x))
    rw [andB_true, Nat.beq_eq, Nat.beq_eq] at h
    apply (H2 * H1).injective
    rw [cg as (as x), cg as x]
    exact enc_injective (by rw [hS, hS, h.1])
  · intro x
    have h := (allB_iff _ _).mp rf _ (enc_lt ((H2 * H1) x))
    rw [andB_true, Nat.beq_eq, Nat.beq_eq] at h
    apply (H2 * H1).injective
    rw [cg as (aq x), cg aq x, cg aq (aq (aq (as x))), cg aq (aq (as x)), cg aq (as x), cg as x]
    apply enc_injective
    rw [hS, hQ, hQ, hQ, hQ, hS]
    exact h.2

theorem fzbClassSpec : FzbClassSpec := by
  intro r aq as ay A
  have hr2 : ∀ x, (r * r) ((r * r) ((r * r) x)) = x := fun x => by
    change r (r (r (r (r (r x))))) = x
    rw [A.r3, A.r3]
  have hf2 : ∀ x, x ≠ 1 → (r * r) x ≠ x := by
    intro x hx e
    change r (r x) = x at e
    apply A.r_fpf x hx
    have h3 := congrArg r e
    rw [A.r3] at h3
    exact h3.symm
  obtain ⟨β, hβ⟩ := FzNorm.fzNormSpec (r * r) hr2 hf2
  have hb : ∀ x, β (r x) = fzRho0 (fzRho0 (β x)) := by
    intro x
    have e : r x = (r * r) ((r * r) x) := by
      change r x = r (r (r (r x)))
      rw [A.r3]
    rw [e, hβ, hβ]
  have A1 := fzbAdm_conj A β
  rw [comm_conj' hb] at A1
  obtain ⟨c, g, hg, hq, hs, hy, h1, h2⟩ := fzb_core A1
  refine ⟨c, g * β, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change g (β (r x)) = fzRho0 (fzRho0 (g (β x)))
    rw [hb, hg]
  · rw [show g * β * aq * (g * β)⁻¹ = g * (β * aq * β⁻¹) * g⁻¹ by group]
    exact hq
  · rw [show g * β * as * (g * β)⁻¹ = g * (β * as * β⁻¹) * g⁻¹ by group]
    exact hs
  · rw [show g * β * ay * (g * β)⁻¹ = g * (β * ay * β⁻¹) * g⁻¹ by group]
    exact hy
  · intro x
    have := h1 (β x)
    simp only [conj_apply, inv_apply_self] at this
    exact β.injective this
  · intro x
    have := h2 (β x)
    simp only [conj_apply, inv_apply_self] at this
    exact β.injective this

end CFSG.KC.FzUT
