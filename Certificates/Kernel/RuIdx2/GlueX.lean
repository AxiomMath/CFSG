module

public import Certificates.Kernel.RuIdx2.Glue
public import Certificates.Kernel.Ru7032.Cover
import Certificates.Kernel.RuIdx2.X
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import Certificates.Kernel.RuIdx2.DefsX

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2.GlueX

open CFSG.KD.RuIdx2 CFSG.KD.RuIdx2.Sem CFSG.KD.RuIdx2.Glue CFSG.KC.RuIdx2 CFSG.KC.SLDc
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert CFSG.Quasithin.H13.LocDbl.RuCov
open CFSG.Quasithin.H13.K1262Two.RuP
open CFSG.KD.RuIdx2.Lab (Rv)
open CFSG.Sporadic.Ru.Native (ruData)

@[instance_reducible] noncomputable def act4060 : MulAction (J ruData) (Fin 4060) :=
  inferInstanceAs (MulAction (J ruData) (Fin ruData.n))

attribute [local instance] act4060

theorem B_eq : ruData.base.toList = Ru4120.B := by decide

theorem ctx : Ru4120.H.Ctx (a ruData) (b ruData) :=
  ⟨Ru.ru_ta, Ru.ru_tb, fun g hg => base_property Ru.ru_facts g (by rw [B_eq]; exact hg)⟩

theorem sgK_eq : ruSgK = [lt (a ruData) (b ruData) 2, lt (a ruData) (b ruData) 3,
    lt (a ruData) (b ruData) 4] := by
  unfold ruSgK ruQp
  simp only [List.map_cons, List.map_nil]
  rw [Ru4120.H.slpElts_ruProg _ _ (by decide), Ru4120.H.slpElts_ruProg _ _ (by decide),
    Ru4120.H.slpElts_ruProg _ _ (by decide)]
  rfl

theorem S_eq : ruS = Ru4120.H.RX (a ruData) (b ruData) := by
  unfold ruS
  rw [sgK_eq, Lab.RX_eq]

theorem G_zero : Ru4120.G.E (a ruData) (b ruData) 0 = a ruData := by
  rw [← Ru4120.H.slpElts_ruProg _ _ (by decide)]
  unfold slpElts
  rw [Ru4120.H.getD_foldl_eltStep _ _ (by simp)]
  rfl

theorem G_one : Ru4120.G.E (a ruData) (b ruData) 1 = b ruData := by
  rw [← Ru4120.H.slpElts_ruProg _ _ (by decide)]
  unfold slpElts
  rw [Ru4120.H.getD_foldl_eltStep _ _ (by simp)]
  rfl

section Let


theorem ruLet_eq : ruLet = #[a ruData, b ruData, lt (a ruData) (b ruData) 2,
    lt (a ruData) (b ruData) 3, lt (a ruData) (b ruData) 4, (lt (a ruData) (b ruData) 2)⁻¹,
    (lt (a ruData) (b ruData) 3)⁻¹, (lt (a ruData) (b ruData) 4)⁻¹] := by
  unfold ruLet
  rw [sgK_eq]
  generalize lt (a ruData) (b ruData) 2 = y2
  generalize lt (a ruData) (b ruData) 3 = y3
  generalize lt (a ruData) (b ruData) 4 = y4
  generalize a ruData = x0
  generalize b ruData = x1
  rfl

theorem arr_getD {G : Type} (L : List G) (i : Nat) (d : G) : L.toArray.getD i d = L.getD i d := by
  simp [List.getD_eq_getElem?_getD]

theorem let_eq {l : Nat} (hl : l < 8) : ruLet.getD l 1 = lt (a ruData) (b ruData) l := by
  rw [ruLet_eq, arr_getD]
  have h5 := (hinv ctx 2 (by norm_num)).symm
  have h6 := (hinv ctx 3 (by norm_num)).symm
  have h7 := (hinv ctx 4 (by norm_num)).symm
  have e5 : IL 2 = 5 := rfl
  have e6 : IL 3 = 6 := rfl
  have e7 : IL 4 = 7 := rfl
  rw [e5] at h5
  rw [e6] at h6
  rw [e7] at h7
  have h0 := G_zero.symm
  have h1 := G_one.symm
  have e0 : Ru4120.G.E (a ruData) (b ruData) 0 = lt (a ruData) (b ruData) 0 := rfl
  have e1 : Ru4120.G.E (a ruData) (b ruData) 1 = lt (a ruData) (b ruData) 1 := rfl
  rw [e0] at h0
  rw [e1] at h1
  interval_cases l
  · simp only [List.getD_cons_zero]
    exact h0
  · simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact h1
  · simp only [List.getD_cons_succ, List.getD_cons_zero]
  · simp only [List.getD_cons_succ, List.getD_cons_zero]
  · simp only [List.getD_cons_succ, List.getD_cons_zero]
  · simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact h5
  · simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact h6
  · simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact h7

theorem ruWord_eq (W : Nat) (hW : ∀ c ∈ unW W, c < 8) :
    ruWord (unW W) = wE (a ruData) (b ruData) W := by
  unfold ruWord evalElt wE
  congr 1
  exact List.map_congr_left fun l hl => let_eq (hW l hl)

theorem ruWord_append (u w : List Nat) : ruWord (u ++ w) = ruWord u * ruWord w := by
  unfold ruWord evalElt
  rw [List.map_append, List.prod_append]

theorem topW_eq : ruTopW = (List.range 839).map fun j => unW (XW j) := by
  have h := CFSG.KD.RuIdx2.topW
  unfold famT at h
  unfold ruTopW
  exact beq_iff_eq.1 h

theorem XW_lt {j : Nat} (hj : j < 839) : ∀ c ∈ unW (XW j), c < 8 := by
  have hm : unW (XW j) ∈ ruTopW := by
    rw [topW_eq]
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  unfold ruTopW at hm
  obtain ⟨r, hr, e⟩ := List.mem_map.1 hm
  have h := Ru7032.ctx.mem_recs_repOK (List.mem_filter.1 hr).1
  unfold repOK at h
  simp only [Bool.and_eq_true] at h
  have hw := h.1.1.1
  unfold isW at hw
  intro c hc
  rw [← e] at hc
  exact Nat.blt_eq.mp (List.all_eq_true.1 hw c hc)

theorem cover_x (g : J ruData) :
    g ∈ ruVA ∨ g ∈ ruVB ∨ ∃ j < 839, ∃ s ∈ Ru4120.H.RX (a ruData) (b ruData),
      ∃ t ∈ Ru4120.H.RX (a ruData) (b ruData), g = s * wE (a ruData) (b ruData) (XW j) * t := by
  rcases Ru7032.cover_el g with h | h | ⟨w, hw, s, hs, t, ht, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rw [topW_eq] at hw
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hw
    have hj' := List.mem_range.1 hj
    rw [S_eq] at hs ht
    exact Or.inr (Or.inr ⟨j, hj', s, hs, t, ht, by rw [ruWord_eq _ (XW_lt hj')]⟩)

end Let

section Groups


theorem card_T : Nat.card (Ru4120.H.RX (a ruData) (b ruData)) = 2 ^ 14 := by
  rw [← S_eq]
  exact Ru7032.card_S

theorem T_le_VA : Ru4120.H.RX (a ruData) (b ruData) ≤ ruVA := by
  rw [← S_eq]
  exact Ru7032.S_le_VA

theorem T_le_VB : Ru4120.H.RX (a ruData) (b ruData) ≤ ruVB := by
  rw [← S_eq]
  exact Ru7032.S_le_VB

theorem noBig_two {u : Nat} (hu : u < 7) (hu2 : u ≠ 2) : NoBig (Rv (a ruData) (b ruData) u) := by
  have hex : ex u = [] := by
    interval_cases u
    all_goals first | rfl | exact absurd rfl hu2
  obtain ⟨hle, -, hcard, hR, hτT, hτR, -⟩ := Lab.idx2_v ctx card_T hu
  refine noBig_of_good_two (P := fun x => ∃ j < 839, x = wE (a ruData) (b ruData) (XW j))
    hle hcard hR hτT hτR (by rw [Ru7032.card_VA]) (by rw [Ru7032.card_VB]) (fun g => ?_) ?_
  · rcases cover_x g with h | h | ⟨j, hj, s, hs, t, ht, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨_, ⟨j, hj, rfl⟩, s, hs, t, ht, rfl⟩)
  · rintro x ⟨j, hj, rfl⟩
    exact ⟨good_x ctx card_T hu hj (by rw [hex]; simp),
      good_tx ctx card_T hu hj (by rw [hex]; simp)⟩

theorem mem_VA {u w : List Nat}
    (h : vaK CFSG.KD.RuDc.C (eMem CFSG.KD.RuDc.C CFSG.KD.RuDc.D 1) u w = true) :
    ruWord w ∈ ruVA := by
  unfold vaK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hw, hm⟩ := h
  have hwl : ∀ l ∈ w, l < 2 + Ru7032.ctx.C.ns := fun l hl =>
    Nat.blt_eq.mp (List.all_eq_true.1 hw l hl)
  have hE : ∀ w ∈ eMem Ru7032.ctx.C Ru7032.ctx.D 1, ∀ l ∈ w, l < 2 + Ru7032.ctx.C.ns := by
    intro w hw l hl
    change w ∈ sLet Ru7032.ctx.C ++ CFSG.KD.RuDc.J.mw.getD 1 [] at hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      rw [List.mem_singleton] at hl
      rw [hl]
      have : i < 6 := List.mem_range.mp hi
      change 2 + i < 2 + 6
      omega
    · rw [RuK.mwJ CFSG.KD.RuDc.facts] at hw
      have := RuK.mw_lt2 (by norm_num) w hw l hl
      change l < 2 + 6
      omega
  obtain ⟨s, hs, u', hu', hlab⟩ := Ru7032.ctx.memW_sound hE hm
  have hlab' : lab ruData.n ptLab Ru7032.ctx.C.Δ (s * u') =
      lab ruData.n ptLab Ru7032.ctx.C.Δ (evalElt Ru7032.ctx.els w) := by
    rw [hlab]
    exact Ru7032.ctx.labF_eq_lab hwl
  have ht : (s * u')⁻¹ * evalElt Ru7032.ctx.els w ∈ Ru7032.ctx.S :=
    (Ru7032.ctx.lab_eq_iff_S _).mp
      ((mem_stab DcSoundCtx.hlaw Ru7032.ctx.hΔ).mp
        ((lab_eq_iff DcSoundCtx.hlaw Ru7032.ctx.hΔ _ _).mp hlab'))
  have hSY : Ru7032.ctx.S ≤ ruVA := by
    rw [Ru7032.S_eq]
    exact Ru7032.S_le_VA
  have huY : u' ∈ ruVA := by
    refine (Subgroup.closure_le _).mpr ?_ hu'
    rintro y ⟨w, hw, rfl⟩
    change w ∈ sLet Ru7032.ctx.C ++ CFSG.KD.RuDc.J.mw.getD 1 [] at hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have : i < 6 := List.mem_range.mp hi
      refine hSY (Ru7032.ctx.evalElt_mem_S fun l hl => ?_)
      rw [List.mem_singleton] at hl
      rw [hl]
      change 2 ≤ 2 + i ∧ 2 + i < 2 + 6
      omega
    · rw [RuK.mwJ CFSG.KD.RuDc.facts] at hw
      rw [Ru7032.ctx.evalElt_eq_wordElt (RuK.mw_lt2 (by norm_num) w hw), Ru7032.VA_eq,
        Ru7032.Y_eq]
      exact Subgroup.subset_closure (List.mem_append_right _ (List.mem_map_of_mem hw))
  have e : evalElt Ru7032.ctx.els w = s * u' * ((s * u')⁻¹ * evalElt Ru7032.ctx.els w) := by
    group
  have hmem : evalElt Ru7032.ctx.els w ∈ ruVA := by
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSY hs) huY) (hSY ht)
  rw [Ru7032.els_eq] at hmem
  exact hmem

theorem tgt_mem {k : Nat} (hk : k < 7) : ruWord (tgt k) ∈ ruVA := by
  have h := CFSG.KD.RuIdx2.X.all k hk
  unfold famX at h
  rw [Bool.and_eq_true] at h
  exact mem_VA h.2

@[expose] noncomputable def cQ : J ruData := ruWord QC

@[expose] noncomputable def W1 : Subgroup (J ruData) := ruVA.map (MulAut.conj cQ).toMonoidHom

@[expose] noncomputable def τ1 : J ruData := lt (a ruData) (b ruData) (tau 2)

@[expose] noncomputable def W2 : Subgroup (J ruData) := W1.map (MulAut.conj τ1).toMonoidHom

theorem mem_map_conj {G : Type} [Group G] (g : G) (K : Subgroup G) {y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem card_map_conj {G : Type} [Group G] (g : G) (K : Subgroup G) :
    Nat.card (K.map (MulAut.conj g).toMonoidHom) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mem_W1 {y : J ruData} : y ∈ W1 ↔ cQ⁻¹ * y * cQ ∈ ruVA :=
  mem_map_conj cQ ruVA

theorem mem_W2 {y : J ruData} : y ∈ W2 ↔ τ1⁻¹ * y * τ1 ∈ W1 :=
  mem_map_conj τ1 W1

theorem card_W1 : Nat.card W1 = 245760 := by
  rw [W1, card_map_conj, Ru7032.card_VA]

theorem card_W2 : Nat.card W2 = 245760 := by
  rw [W2, card_map_conj, card_W1]

theorem mem_W1_of {y : J ruData} (h : ruWord QCI * (y * cQ) ∈ ruVA) : y ∈ W1 := by
  have h0 : ruWord QCI * cQ ∈ ruVA := by
    have h1 := tgt_mem (k := 0) (by norm_num)
    have e : tgt 0 = QCI ++ QC := rfl
    rwa [e, ruWord_append] at h1
  rw [mem_W1]
  have e : cQ⁻¹ * y * cQ = (ruWord QCI * cQ)⁻¹ * (ruWord QCI * (y * cQ)) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h0) h

theorem R_le_W1 : Rv (a ruData) (b ruData) 2 ≤ W1 := by
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl4 : l < 4 := List.mem_range.1 hl
  refine mem_W1_of ?_
  have h := tgt_mem (k := 1 + l) (by omega)
  have e : tgt (1 + l) = QCI ++ (unW (RG 2 l) ++ QC) := by
    interval_cases l <;> rfl
  have hRG : ∀ c ∈ unW (RG 2 l), c < 8 := by
    interval_cases l <;> decide
  rwa [e, ruWord_append, ruWord_append, ruWord_eq _ hRG] at h

theorem x820_mem : wE (a ruData) (b ruData) (XW 820) ∈ W1 := by
  refine mem_W1_of ?_
  have h := tgt_mem (k := 5) (by norm_num)
  have e : tgt 5 = QCI ++ (unW (XW 820) ++ QC) := rfl
  rwa [e, ruWord_append, ruWord_append, ruWord_eq _ (XW_lt (by norm_num))] at h

theorem x824_mem : wE (a ruData) (b ruData) (XW 824) ∈ W2 := by
  rw [mem_W2]
  refine mem_W1_of ?_
  have h := tgt_mem (k := 6) (by norm_num)
  have e : tgt 6 = QCI ++ ([7] ++ (unW (XW 824) ++ ([4] ++ QC))) := rfl
  have h7 : ruWord [7] = τ1⁻¹ := by
    unfold ruWord evalElt τ1
    rw [List.map_singleton, List.prod_singleton, let_eq (by norm_num)]
    exact hinv ctx 4 (by norm_num)
  have h4 : ruWord [4] = τ1 := by
    unfold ruWord evalElt τ1
    rw [List.map_singleton, List.prod_singleton, let_eq (by norm_num)]
    rfl
  rw [e, ruWord_append, ruWord_append, ruWord_append, ruWord_append, h7, h4,
    ruWord_eq _ (XW_lt (by norm_num))] at h
  have e2 : τ1⁻¹ * wE (a ruData) (b ruData) (XW 824) * τ1 * cQ =
      τ1⁻¹ * (wE (a ruData) (b ruData) (XW 824) * (τ1 * cQ)) := by group
  rw [e2]
  exact h

theorem tau1_inv : τ1⁻¹ = τ1 := inv_eq_of_mul_eq_one_right (tau_sq ctx)

theorem noBig_001 : NoBig (Rv (a ruData) (b ruData) 2) := by
  have hex : ex 2 = [1640, 1648] := rfl
  obtain ⟨hle, -, hcard, hR, hτT, hτR, -⟩ := Lab.idx2_v ctx card_T (u := 2) (by norm_num)
  have g820 : Good (Rv (a ruData) (b ruData) 2) (Ru4120.H.RX (a ruData) (b ruData))
      (τ1 * wE (a ruData) (b ruData) (XW 820)) :=
    good_tx ctx card_T (u := 2) (by norm_num) (j := 820) (by norm_num) (by rw [hex]; decide)
  have g824 : Good (Rv (a ruData) (b ruData) 2) (Ru4120.H.RX (a ruData) (b ruData))
      (τ1 * wE (a ruData) (b ruData) (XW 824)) :=
    good_tx ctx card_T (u := 2) (by norm_num) (j := 824) (by norm_num) (by rw [hex]; decide)
  refine noBig_of_good_four (W1 := W1) (W2 := W2) (τ := τ1)
    (P := fun x => ∃ j < 839, j ≠ 820 ∧ j ≠ 824 ∧ x = wE (a ruData) (b ruData) (XW j))
    (Q := fun x => x = wE (a ruData) (b ruData) (XW 820) ∨ x = wE (a ruData) (b ruData) (XW 824))
    hle hcard hR hτT hτR (hle.trans T_le_VA) (hle.trans T_le_VB) R_le_W1 (fun r hr => ?_)
    (by rw [Ru7032.card_VA]) (by rw [Ru7032.card_VB]) (by rw [card_W1]) (by rw [card_W2])
    (fun y hy => ?_) (fun y hy => ?_) (fun g => ?_) ?_ ?_
  · rw [mem_W2]
    refine R_le_W1 ?_
    have h := conj_mem_two hle hcard (Subgroup.inv_mem _ hτT) hr
    rwa [inv_inv] at h
  · rw [mem_W2]
    have e : τ1⁻¹ * (τ1 * y * τ1⁻¹) * τ1 = y := by group
    rwa [e]
  · rw [mem_W2] at hy
    have e : τ1 * y * τ1⁻¹ = τ1⁻¹ * y * τ1 := by rw [tau1_inv]
    rwa [e]
  · rcases cover_x g with h | h | ⟨j, hj, s, hs, t, ht, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨_, ?_, s, hs, t, ht, rfl⟩)
      by_cases h1 : j = 820
      · exact Or.inr (Or.inl (by rw [h1]))
      by_cases h2 : j = 824
      · exact Or.inr (Or.inr (by rw [h2]))
      exact Or.inl ⟨j, hj, h1, h2, rfl⟩
  · rintro x ⟨j, hj, h1, h2, rfl⟩
    have n1 : 2 * j ∉ ex 2 := by
      rw [hex]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have n2 : 2 * j + 1 ∉ ex 2 := by
      rw [hex]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have g1 := good_x ctx card_T (u := 2) (by norm_num) hj n1
    have g2 := good_tx ctx card_T (u := 2) (by norm_num) hj n2
    exact ⟨g1, g2⟩
  · rintro x (rfl | rfl)
    · exact ⟨Or.inl x820_mem, g820⟩
    · exact ⟨Or.inr x824_mem, g824⟩

end Groups

end CFSG.KD.RuIdx2.GlueX

end
