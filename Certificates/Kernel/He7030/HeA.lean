module

public import Certificates.Kernel.He7030.AK
public import Certificates.Kernel.He7030.HeB
public import Certificates.Kernel.He2111.Final
public import Certificates.Kernel.He7030.OuterU
public import CFSG.Quasithin.H13.HeAutInnerCore

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He7030

open CFSG.KC.PtEnum CFSG.KC.E64F CFSG.KC.SLDc CFSG.KD.HeDc CFSG.KC.He2111
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Sporadic.He (J a b)
open CFSG.Sporadic.HeldB CFSG.KD.He7030.OuterU
open CFSG.Monster.B.Co2 (Rep)
open CFSG.Quasithin.H13.LocDbl.AutInner

theorem br_val (y : Fin 8330) :
    (heBridgePerm y : ℕ) = BR y := by
  rw [← rep_heBridge y, CFSG.KD.He2111.br_get y.isLt]
  rfl

theorem bri_val (y : Fin 8330) :
    (heBridgePerm⁻¹ y : ℕ) = BI y := by
  have h := (CFSG.KD.He2111.brK_spec (heBridgePerm⁻¹ y).isLt).2.2.2.1
  have e : e14 (CFSG.KD.He2111.BrT.F 0) (heBridgePerm⁻¹ y : ℕ) = y := by
    rw [← BR, ← br_val, pinv]
  rw [e] at h
  exact h.symm

theorem r_val (y : Fin 8330) : (heAutR y : ℕ) = RR y := by
  rw [← rep_heAutR y, CertificateChecks.KernelSporSch.HeO16.R_eq,
    CertificateChecks.KernelSporSch.HeO16.unpackGet y.isLt]
  rfl

theorem pow_val :
    ∀ (k : ℕ) (y : Fin 8330), ((heAutR ^ k) y : ℕ) = RR^[k] y
  | 0, _ => rfl
  | k + 1, y => by
    rw [pow_succ, Equiv.Perm.mul_apply, pow_val k, r_val, Function.iterate_succ_apply]

theorem u_val (y : Fin 8330) :
    (heAutU y : ℕ) = RR (RR (RR (RR (RR y)))) := by
  rw [heAutU, pow_val]
  rfl

theorem u_inv : heAutU⁻¹ = heAutU :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, heAutU_sq])


theorem uJ_val (j : Fin 8330) :
    (heBridgePerm (heAutU (heBridgePerm⁻¹ j)) : ℕ) = uJ j := by
  rw [br_val, u_val, bri_val]
  rfl

theorem uJ_lt {q : ℕ} (hq : q < 8330) : uJ q < 8330 := by
  have := uJ_val ⟨q, hq⟩
  rw [← this]
  exact Fin.is_lt _

theorem act_xiU (g : J) {q : ℕ} (hq : q < 8330) :
    act 8330 (xiU g) q = uJ (act 8330 g (uJ q)) := by
  have e1 := act_eq (xiU g) ⟨q, hq⟩
  rw [xiU_smul, u_inv] at e1
  rw [e1, uJ_val, ← act_eq g, uJ_val]

theorem good_of_act {x : J} {f : ℕ → ℕ} (h : ∀ p < 8330, act 8330 x p = f p) :
    Good 8330 (tab 8330 x).toArray f := by
  refine ⟨by simp [tab], fun p hp => ?_⟩
  have e : (tab 8330 x).toArray.getD p 0 = act 8330 x p := img_tab x p
  rw [e, h p hp]
  exact ⟨rfl, h p hp ▸ act_lt x hp⟩

@[irreducible] noncomputable def wE : J := wordElt a b Dt.w

@[irreducible] noncomputable def xi : MulAut J := MulAut.conj wE * xiU

theorem xi_eq : xi = MulAut.conj wE * xiU := by unfold xi; rfl

theorem xi_apply (g : J) : xi g = wE * xiU g * wE⁻¹ := by
  rw [xi_eq]
  rfl

theorem wE_eq : wE = wordElt a b Dt.w := by unfold wE; rfl

structure AFacts : Prop where
  lt : ∀ l ∈ Dt.w, l < 2
  inv : invB (wordF L Dt.w) (wordF L (invW Dt.w)) = true
  fix : ∀ l ∈ [2, 3, 4, 5], labF (xiF (L l)) Δ = Δ
  move : ∀ k ∈ [3, 4], (Om k).lbl.toList.contains (labF (xiF (wordF L (mW k))) Δ) = false

theorem a_facts : AFacts := by
  have h := a_ok
  unfold aChk at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem good_xi {g : J} {f : ℕ → ℕ} (hg : Good 8330 (tab 8330 g).toArray f) :
    Good 8330 (tab 8330 (xi g)).toArray (xiF f) := by
  have hw : Good 8330 (tab 8330 wE).toArray (wordF L Dt.w) := by
    rw [wE_eq]; exact good_we a_facts.lt
  have hwi := good_we (invW_lt Dt.w)
  have e : wordElt a b (invW Dt.w) = wE⁻¹ := inv_of_base hw hwi a_facts.inv
  refine good_of_act fun p hp => ?_
  have h1 := act_of_good hwi hp
  rw [e] at h1
  have hq := h1.2
  have hf := act_of_good hg (uJ_lt hq)
  rw [xi_apply, act_mul _ _ hp, h1.1, act_mul _ _ hq, act_xiU g hq, hf.1,
    (act_of_good hw (uJ_lt hf.2)).1]
  rfl

theorem lab_of {x : J} {f : ℕ → ℕ} (hx : Good 8330 (tab 8330 x).toArray f) :
    lab 8330 ptLab heDelta x = labF f Δ := by
  change ptAct (tab 8330 x).toArray heDelta = _
  rw [CFSG.KC.SLOm.ptAct_good hx delta_lt]
  rfl

theorem xi_S : (aimg (P := J) xi heCtxK.S : Subgroup J) = heCtxK.S := by
  have hle : (aimg (P := J) xi heCtxK.S : Subgroup J) ≤ heCtxK.S := by
    rw [aimg, ← heCtxK.hSeq, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [heCtxK.hSeq]
    change s ∈ heSg at hs
    rw [heSg_eq] at hs
    have key : ∀ i < 4, xi (E (heQp.getD i (0, 0)).1) ∈ heCtxK.S := by
      intro i hi
      change lab 8330 ptLab heDelta _ = heDelta
      rw [lab_of (good_xi (s_pair hi).1)]
      have h := a_facts.fix (Nat.add 2 i) (by interval_cases i <;> decide)
      rw [h]
      rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact key 0 (by decide)
    · exact key 1 (by decide)
    · exact key 2 (by decide)
    · exact key 3 (by decide)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_aimg])

theorem xi_moves {k : ℕ} (hk : k = 3 ∨ k = 4) : (aimg (P := J) xi (heCtxK.Y k) : Subgroup J) ≠ heCtxK.Y k := by
  intro h
  have ho := ord_k hk
  have hm : mE k ∈ heCtxK.Y k := by
    rw [Y_k hk]
    exact Subgroup.subset_closure (by simp)
  have hx : xi (mE k) ∈ heCtxK.Y k := by
    rw [← h]
    exact mem_aimg.2 ⟨mE k, hm, rfl⟩
  have hk11 : k < 11 := by rcases hk with rfl | rfl <;> decide
  have hJ : k < heCtxK.J := by rw [heK_J]; exact hk11
  obtain ⟨x, hxs, e⟩ := (heCtxK.Y_mem_iff hJ _).1 hx
  have hOm : heCtxK.D.Om[k]! = Om k := by rw [heK_D_Om, Om_get hk11]
  have hl : lab 8330 ptLab heDelta (xi (mE k)) = labF (xiF (wordF L (mW k))) Δ :=
    lab_of (good_xi (good_we ho.mlt))
  have hmv := a_facts.move k (by rcases hk with rfl | rfl <;> decide)
  rw [hOm] at hxs e
  change lab 8330 ptLab heDelta _ = _ at e
  rw [hl, getElem!_pos _ x hxs] at e
  rw [e] at hmv
  have : (Om k).lbl.toList.contains (Om k).lbl[x] = true := by
    rw [List.contains_iff_mem, Array.mem_toList_iff]
    exact Array.getElem_mem hxs
  rw [this] at hmv
  exact absurd hmv (by decide)

theorem incl_cover {j : ℕ} (hj : j < 11) :
    3 ∈ heIncl[j]! ∨ 4 ∈ heIncl[j]! ∨ 7 ∈ heIncl[j]! := by
  interval_cases j <;> decide

theorem he_aK : ∃ R W₁ W₂ W₃ : Subgroup J, Nat.card R = 2 ^ 10 ∧ R ≤ W₁ ∧ R ≤ W₂ ∧
    Nat.card W₁ = 138240 ∧ Nat.card W₂ = 138240 ∧ Nat.card W₃ = 21504 ∧
    (∀ Y : Subgroup J, R ≤ Y → Y ≠ ⊤ → Y ≤ W₁ ∨ Y ≤ W₂ ∨ Y ≤ W₃) ∧
    ∃ w : J, (aimg (P := J) (MulAut.conj w * xiU) R : Subgroup J) = R ∧
      (aimg (P := J) (MulAut.conj w * xiU) W₁ : Subgroup J) ≠ W₁ ∧
      (aimg (P := J) (MulAut.conj w * xiU) W₂ : Subgroup J) ≠ W₂ := by
  refine ⟨heCtxK.S, heCtxK.Y 3, heCtxK.Y 4, heCtxK.Y 7, by rw [heK_card_S]; norm_num,
    heCtxK.S_le_Y 3, heCtxK.S_le_Y 4, by rw [heK_member_card 3 (by decide)]; rfl,
    by rw [heK_member_card 4 (by decide)]; rfl, by rw [heK_member_card 7 (by decide)]; rfl,
    fun Y hSY hY => ?_, wE, by rw [← xi_eq]; exact xi_S,
    by rw [← xi_eq]; exact xi_moves (Or.inl rfl), by rw [← xi_eq]; exact xi_moves (Or.inr rfl)⟩
  obtain ⟨j, -, rfl⟩ := heK_complete Y hSY
  unfold memberOrTop at hY ⊢
  by_cases h : j < 11
  · rw [if_pos h]
    rcases incl_cover h with h3 | h4 | h7
    · exact Or.inl ((heK_Y_le_iff h (by decide)).2 h3)
    · exact Or.inr (Or.inl ((heK_Y_le_iff h (by decide)).2 h4))
    · exact Or.inr (Or.inr ((heK_Y_le_iff h (by decide)).2 h7))
  · rw [if_neg h] at hY
    exact absurd rfl hY

theorem heAutInner_JK :
    ∀ S B : Subgroup J, Nat.card S = 2 ^ 10 → S ≤ Subgroup.normalizer (B : Set J) →
      Nat.card B = 69120 → ∀ f : MulAut J, (aimg (P := J) f B : Subgroup J) = B →
        ∃ k : J, ∀ x, f x = k * x * k⁻¹ := by
  intro S B hS hSB hB f hfB
  obtain ⟨R, W₁, W₂, W₃, hR, hRW₁, hRW₂, h₁, h₂, h₃, hcls, w, hξR, hξ₁, hξ₂⟩ := he_aK
  have hO : ∀ f : MulAut J, (∃ k : J, ∀ x, f x = k * x * k⁻¹) ∨
      (∃ k : J, ∀ x, f x = k * (MulAut.conj w * xiU) x * k⁻¹) := by
    intro f
    rcases hOutU f with h | ⟨k, hk⟩
    · exact Or.inl h
    · refine Or.inr ⟨k * w⁻¹, fun x => ?_⟩
      rw [hk]
      change k * xiU x * k⁻¹ = k * w⁻¹ * (w * xiU x * w⁻¹) * (k * w⁻¹)⁻¹
      group
  have hnn : ∀ N : Subgroup J, N.Normal → Nat.card N ≠ 69120 := by
    intro N hN
    have := hN
    rcases CFSG.Sporadic.He.isSimpleGroup_J.eq_bot_or_eq_top_of_normal N with h | h
    · rw [h, Subgroup.card_bot]; norm_num
    · rw [h, Subgroup.card_top, CFSG.Sporadic.He.card_J]; norm_num
  exact aut_stab_inner (P := J) CFSG.Sporadic.He.card_J hnn hR hRW₁ hRW₂ h₁ h₂ h₃ hcls _ hξR hξ₁
    hξ₂ hO hS hSB hB hfB

end CFSG.KD.He7030

end
