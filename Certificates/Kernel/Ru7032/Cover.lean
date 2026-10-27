module

public import CFSG.Quasithin.H13.LocDblRuCoverInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import Certificates.Kernel.RuDc.Final
public import Certificates.Kernel.RuDc.Facts
public import CFSG.Certificates.Kernel.SporLatDcCoset
public import CFSG.Certificates.Kernel.SporLatDcMem

public section

namespace CFSG.KD.Ru7032

set_option maxRecDepth 100000

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert CFSG.Quasithin.H13.LocDbl.RuCov
open CFSG.Sporadic.Ru.Native (ruData)

@[expose] noncomputable def slR : List (J ruData) := ruSgK ++ ruSgK.map (·⁻¹)

theorem sgK_eq : ruSgK = [RuK.E 163, RuK.E 172, RuK.E 185] := RuK.ruSg_eq

theorem inv_node {i : ℕ}
    (hi : i < 3) :
    RuK.E (CFSG.KD.RuDc.nodes.getD (Nat.add 5 i) 0) =
      (RuK.E (CFSG.KD.RuDc.nodes.getD (Nat.add 2 i) 0))⁻¹ :=
  RuK.eq_inv_of_maps (RuK.good_L CFSG.KD.RuDc.facts (by change 5 + i < 8; omega))
    (RuK.good_L CFSG.KD.RuDc.facts (by change 2 + i < 8; omega))
    (RuK.hinvL CFSG.KD.RuDc.facts i hi)

theorem slR_eq :
    slR = [RuK.E 163, RuK.E 172, RuK.E 185, RuK.E 198, RuK.E 203, RuK.E 207] := by
  have h0 : RuK.E 198 = (RuK.E 163)⁻¹ := inv_node (i := 0) (by decide)
  have h1 : RuK.E 203 = (RuK.E 172)⁻¹ := inv_node (i := 1) (by decide)
  have h2 : RuK.E 207 = (RuK.E 185)⁻¹ := inv_node (i := 2) (by decide)
  unfold slR
  rw [sgK_eq, h0, h1, h2]
  rfl

theorem take_slR : slR.take 3 = ruSgK := by
  unfold slR
  rw [sgK_eq]
  rfl

theorem let_eq {l : ℕ} (hl : l < 8) :
    (a ruData :: b ruData :: slR).getD l 1 = RuK.E (CFSG.KD.RuDc.nodes.getD l 0) := by
  rw [slR_eq]
  interval_cases l
  · exact RuK.E0.symm
  · exact RuK.E1.symm
  all_goals rfl

theorem hLR :
    ∀ l < 2 + CFSG.KD.RuDc.C.ns, Good ruData.n
      (tab ruData.n ((a ruData :: b ruData :: slR).getD l 1)).toArray (CFSG.KD.RuDc.C.L l) := by
  intro l hl
  have hl' : l < 8 := hl
  rw [let_eq hl']
  exact RuK.good_L CFSG.KD.RuDc.facts hl'

theorem hSR : ∀ x ∈ slR, x ∈ Subgroup.closure {x | x ∈ slR.take CFSG.KD.RuDc.C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ slR.take 3}
  rw [take_slR]
  rcases List.mem_append.mp hx with hx | hx
  · exact Subgroup.subset_closure hx
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.inv_mem _ (Subgroup.subset_closure hy)

@[expose] noncomputable def ctx :
    DcSoundCtx (J ruData) ruData.n :=
  ⟨CFSG.KD.RuDc.C, CFSG.KD.RuDc.D, rfl, a ruData, b ruData, closure_ab ruData, slR,
    (by rw [slR_eq]; rfl), hLR, hSR, 2 ^ 14,
    (by
      change Nat.card (Subgroup.closure {x | x ∈ slR.take 3}) = 2 ^ 14
      rw [take_slR]
      exact RuK.ru_sGens.2),
    (by
      change Nat.card (J ruData) = 8906625 * 2 ^ 14
      rw [RuK.ru_card, mul_comm]),
    RuK.hsep CFSG.KD.RuDc.facts, (by decide),
    (by
      have h := CFSG.KD.RuDc.facts.1.1
      rw [dcCheck_eq_dcCheckS] at h
      exact h)⟩

section Ctx


theorem S_eq : ctx.S = ruS := by
  change Subgroup.closure {x | x ∈ slR.take 3} = _
  rw [take_slR]
  rfl

theorem els_eq : ctx.els = ruLet := by
  unfold DcSoundCtx.els ruLet
  change (a ruData :: b ruData :: slR).toArray = _
  unfold slR
  rfl

theorem recs_eq : ctx.recs = CFSG.KD.RuDc.D.Rc.flatten := rfl

theorem mw_len : CFSG.KD.RuDc.D.mw.length = 5 := by
  rw [CFSG.KD.RuDc.facts.1.2.2.1]
  rfl

theorem atom {r : Rep} (hr : r ∈ ctx.recs) :
    atomR CFSG.KD.RuDc.C CFSG.KD.RuDc.D r = true := by
  have h := ctx.mem_recs_repOK hr
  change repOK CFSG.KD.RuDc.C CFSG.KD.RuDc.D r = true at h
  unfold repOK at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem cls_le {r : Rep} (hr : r ∈ ctx.recs) (h5 : ¬ r.cls < 5) : r.cls = 5 := by
  have h := atom hr
  unfold atomR at h
  rw [mw_len] at h
  have hb : Nat.blt r.cls 5 = false := by
    cases hc : Nat.blt r.cls 5
    · rfl
    · exact absurd (Nat.blt_eq.mp hc) h5
  rw [hb, cond_false, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem Y_eq (j : ℕ) :
    Ru.ruCtx.Y j =
      Subgroup.closure {x | x ∈ ruSgK ++ (ruMw[j]!).map (wordElt (a ruData) (b ruData))} :=
  rfl

theorem S_le_Y (j : ℕ) : ruS ≤ Ru.ruCtx.Y j := by
  rw [Y_eq]
  exact Subgroup.closure_mono fun x hx => List.mem_append_left _ hx

theorem mem_Y {r : Rep} (hr : r ∈ ctx.recs) (hc : r.cls < 5) :
    evalElt ctx.els r.w ∈ Ru.ruCtx.Y r.cls := by
  have h := atom hr
  unfold atomR at h
  rw [mw_len] at h
  have hb : Nat.blt r.cls 5 = true := Nat.blt_eq.mpr hc
  rw [hb, cond_true] at h
  split at h
  · rw [Bool.and_eq_true] at h
    have hE : ∀ w ∈ eMem ctx.C ctx.D r.cls, ∀ l ∈ w, l < 2 + ctx.C.ns := by
      intro w hw l hl
      change w ∈ sLet ctx.C ++ CFSG.KD.RuDc.J.mw.getD r.cls [] at hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        rw [List.mem_singleton] at hl
        rw [hl]
        have : i < 6 := List.mem_range.mp hi
        change 2 + i < 2 + 6
        omega
      · rw [RuK.mwJ CFSG.KD.RuDc.facts] at hw
        have := RuK.mw_lt2 hc w hw l hl
        change l < 2 + 6
        omega
    obtain ⟨s, hs, u, hu, hlab⟩ := ctx.memW_sound hE h.1
    rw [ctx.recs_lab_eq hr] at hlab
    have ht : (s * u)⁻¹ * evalElt ctx.els r.w ∈ ctx.S :=
      (ctx.lab_eq_iff_S _).mp
        ((mem_stab DcSoundCtx.hlaw ctx.hΔ).mp ((lab_eq_iff DcSoundCtx.hlaw ctx.hΔ _ _).mp hlab))
    have hSY : ctx.S ≤ Ru.ruCtx.Y r.cls := by
      rw [S_eq]
      exact S_le_Y r.cls
    have huY : u ∈ Ru.ruCtx.Y r.cls := by
      refine (Subgroup.closure_le _).mpr ?_ hu
      rintro y ⟨w, hw, rfl⟩
      change w ∈ sLet ctx.C ++ CFSG.KD.RuDc.J.mw.getD r.cls [] at hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        have : i < 6 := List.mem_range.mp hi
        refine hSY (ctx.evalElt_mem_S fun l hl => ?_)
        rw [List.mem_singleton] at hl
        rw [hl]
        change 2 ≤ 2 + i ∧ 2 + i < 2 + 6
        omega
      · rw [RuK.mwJ CFSG.KD.RuDc.facts] at hw
        rw [ctx.evalElt_eq_wordElt (RuK.mw_lt2 hc w hw), Y_eq]
        exact Subgroup.subset_closure (List.mem_append_right _ (List.mem_map_of_mem hw))
    have e : evalElt ctx.els r.w = s * u * ((s * u)⁻¹ * evalElt ctx.els r.w) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSY hs) huY) (hSY ht)
  · exact absurd h (by simp)

end Ctx

section Lattice


theorem VA_eq : ruVA = Ru.ruCtx.Y 1 := rfl

theorem VB_eq : ruVB = Ru.ruCtx.Y 2 := rfl

theorem Y_le {j : ℕ} (hj : j < 5) : Ru.ruCtx.Y j ≤ ruVA ∨ Ru.ruCtx.Y j ≤ ruVB := by
  rw [VA_eq, VB_eq, Ru.ru_Y_le_iff hj (by norm_num), Ru.ru_Y_le_iff hj (by norm_num)]
  interval_cases j <;> decide

theorem card_S : Nat.card ruS = 2 ^ 14 := RuK.ru_sGens.2

theorem card_VA : Nat.card ruVA = 245760 := by
  rw [VA_eq, Ru.ru_member_card 1 (by norm_num)]
  rfl

theorem card_VB : Nat.card ruVB = 344064 := by
  rw [VB_eq, Ru.ru_member_card 2 (by norm_num)]
  rfl

theorem S_le_VA : ruS ≤ ruVA := S_le_Y 1

theorem S_le_VB : ruS ≤ ruVB := S_le_Y 2

theorem over_le (Y : Subgroup (J ruData)) (hY : ruS ≤ Y) (hne : Y ≠ ⊤) : Y ≤ ruVA ∨ Y ≤ ruVB := by
  have hS : Ru.ruCtx.S ≤ Y := by
    rw [← Ru.ruCtx.hSeq]
    exact hY
  obtain ⟨j, -, rfl⟩ := Ru.ru_complete Y hS
  unfold memberOrTop at hne ⊢
  by_cases hj : j < 5
  · rw [if_pos hj]
    exact Y_le hj
  · exact absurd (if_neg hj) hne

theorem cover_el (g : J ruData) :
    g ∈ ruVA ∨ g ∈ ruVB ∨ ∃ w ∈ ruTopW, ∃ s ∈ ruS, ∃ t ∈ ruS, g = s * ruWord w * t := by
  obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := ctx.cover_rec g
  rw [S_eq] at hs ht
  by_cases hc : r.cls < 5
  · have hY := mem_Y hr hc
    have hsY := S_le_Y r.cls hs
    have htY := S_le_Y r.cls ht
    have hg : s * evalElt ctx.els r.w * t ∈ Ru.ruCtx.Y r.cls :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hsY hY) htY
    rcases Y_le hc with h | h
    · exact Or.inl (h hg)
    · exact Or.inr (Or.inl (h hg))
  · refine Or.inr (Or.inr ⟨r.w, ?_, s, hs, t, ht, ?_⟩)
    · rw [recs_eq] at hr
      exact List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp [cls_le hr hc]⟩, rfl⟩
    · rw [els_eq]
      rfl

theorem cover :
    Nat.card ruS = 2 ^ 14 ∧ ruS ≤ ruVA ∧ ruS ≤ ruVB ∧
      Nat.card ruVA = 245760 ∧ Nat.card ruVB = 344064 ∧
      (∀ Y : Subgroup (J ruData), ruS ≤ Y → Y ≠ ⊤ → Y ≤ ruVA ∨ Y ≤ ruVB) ∧
      ∀ g : J ruData,
        g ∈ ruVA ∨ g ∈ ruVB ∨ ∃ w ∈ ruTopW, ∃ s ∈ ruS, ∃ t ∈ ruS, g = s * ruWord w * t :=
  ⟨card_S, S_le_VA, S_le_VB, card_VA, card_VB, over_le, cover_el⟩

end Lattice

end CFSG.KD.Ru7032

end
