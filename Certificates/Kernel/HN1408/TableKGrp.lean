module

public import Certificates.Kernel.HN1408.TableKGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKSpec
public import Certificates.Kernel.HN1408.CzTFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TK

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.KC.BfsPin CFSG.KC.Blk CFSG.KD.HN1408 CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

abbrev Qk : Subgroup (Equiv.Perm (Fin 1408)) := closure (elemW '' {w | w ∈ qWordsK})
abbrev Ek : Subgroup (Equiv.Perm (Fin 1408)) := closure (elemW '' {w | w ∈ eWordsK})
abbrev Zk : Subgroup (Equiv.Perm (Fin 1408)) := closure (elemW '' {w | w ∈ zcWordsK})

theorem nEq {X Y : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y g) : X = Y := by
  obtain ⟨-, hw, h1, -⟩ := CFSG.KS.PF.canon_facts hX.1
  obtain ⟨-, -, h2, -⟩ := CFSG.KS.PF.canon_facts hY.1
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) h1 h2 fun i hi =>
    (repC_pt hX hi).trans (repC_pt hY hi).symm

theorem eqB_iff {X Y : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y h) :
    Nat.beq X Y = true ↔ g = h := by
  constructor
  · intro e
    rw [Nat.eq_of_beq_eq_true e] at hX
    exact eq_of_repC hX hY
  · rintro rfl
    rw [nEq hX hY]
    exact Nat.beq_refl _

theorem comm_iff {X Y : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y h) :
    commP X Y = true ↔ g * h = h * g :=
  eqB_iff (repC_pc hX hY) (repC_pc hY hX)

theorem nb {a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : Nat.beq a b = false := by
  revert h
  cases Nat.beq a b <;> decide

theorem ne_of {X Y : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y h)
    (hb : bIf(Nat.beq X Y, false, true) = true) : g ≠ h := by
  intro e
  have h1 := (eqB_iff hX hY).2 e
  rw [nb hb] at h1
  cases h1

theorem bIf26773 (c t e : Bool) : bIf(c, t, e) = (if c = true then t else e) := by cases c <;> rfl

theorem cov_of {ws : List (List Nat)} {m cnt : Nat} {T PL : Nat → Nat}
    (r : RecFacts ws m cnt T PL) :
    Nat.card ↥(closure (elemW '' {w | w ∈ ws})) = m ∧
      (∀ g ∈ closure (elemW '' {w | w ∈ ws}), ∃ i < cnt, RepC (T i) g) ∧
      (∀ i < cnt, ∃ g ∈ closure (elemW '' {w | w ∈ ws}), RepC (T i) g) := by
  obtain ⟨e1, e2, hT⟩ := r
  obtain ⟨hc, hE⟩ := enumW_spec e1
  rw [e2] at hE
  refine ⟨hc, fun g hg => ?_, fun i hi => ?_⟩
  · obtain ⟨k, hk, hr⟩ := hE.cov g hg
    have hk' : k < cnt := by simpa [hRec] using hk
    rw [hRec_get hk'] at hr
    exact ⟨k, hk', hT k hk', hr⟩
  · obtain ⟨g, hg, hr⟩ := hE.rep i (by simpa [hRec] using hi)
    rw [hRec_get hi] at hr
    exact ⟨g, hg, hT i hi, hr⟩

theorem gen_of {ws : List (List Nat)} {k m cnt : Nat} {G GI GJ T PL : Nat → Nat}
    (hl : ∀ w ∈ ws, lettersOK w = true) (h : headI ws k m G GI GJ T PL cnt = true) :
    ∀ j < k, RepC (GI j) (elemW (ws.getD j [])) := by
  intro j hj
  obtain ⟨-, hg, -, -⟩ := headI_spec h
  rw [(hg j hj).1]
  exact repC_word (lettersOK_getD hl j)

theorem of_gens {ws : List (List Nat)} {k : Nat} (hk : ws.length = k)
    {P : Equiv.Perm (Fin 1408) → Prop} (h : ∀ j < k, P (elemW (ws.getD j []))) :
    ∀ s ∈ elemW '' {w | w ∈ ws}, P s := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  rw [← List.getD_eq_getElem _ [] hj]
  exact h j (hk ▸ hj)

theorem cQ : TKQ.cnt = 32 := (headI_spec hdQ).2.2.1
theorem cE : TKE.cnt = 8 := (headI_spec hdE).2.2.1
theorem cZ : TKZ.cnt = 8 := (headI_spec hdZ).2.2.1

theorem card_Q : Nat.card ↥Qk = 32 := (cov_of rQ).1
theorem card_E : Nat.card ↥Ek = 8 := (cov_of rE).1
theorem card_Z : Nat.card ↥Zk = 8 := (cov_of rZ).1

theorem c_parts : TKC 0 < 32 ∧ TKQ.T (TKC 0) = specK nK cSpecK ∧ TKC 1 < 8 ∧
    TKZ.T (TKC 1) = TKQ.T (TKC 0) ∧ bIf(Nat.beq (TKQ.T (TKC 0)) idK, false, true) = true ∧
    Nat.beq (pc (TKQ.T (TKC 0)) (TKQ.T (TKC 0))) idK = true ∧
    (∀ j < 3, TKP j < 32 ∧ TKQ.T (TKP j) = TKE.GI j) ∧
    (∀ j < 3, ∀ l < 3, commP (TKE.GI j) (TKE.GI l) = true) ∧
    (∀ i < 8, Nat.beq (pc (TKE.T i) (TKE.T i)) idK = true) := by
  have h := ch26773_c
  simp only [strictB_app, bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a2, Nat.blt_eq.mp a3,
    Nat.eq_of_beq_eq_true a4, a5, a6, fun j hj => ?_, fun j hj l hl => ?_,
    fun i hi => allN_spec a9 i hi⟩
  · have h := allN_spec a7 j hj
    simp only [bAnd_iff] at h
    exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩
  · exact allN_spec (allN_spec a8 j hj) l hl

theorem lC : lettersOK cWordK = true := lettersOK_specWord lN cSpecK

theorem repc : RepC (TKQ.T (TKC 0)) (elemW cWordK) := by
  rw [c_parts.2.1, nspec_eq]
  exact repC_word lC

theorem c_mem_Q : elemW cWordK ∈ Qk := by
  obtain ⟨g, hg, hr⟩ := (cov_of rQ).2.2 (TKC 0) (by rw [cQ]; exact c_parts.1)
  rw [eq_of_repC repc hr]
  exact hg

theorem c_mem_Z : elemW cWordK ∈ Zk := by
  obtain ⟨g, hg, hr⟩ := (cov_of rZ).2.2 (TKC 1) (by rw [cZ]; exact c_parts.2.2.1)
  rw [c_parts.2.2.2.1] at hr
  rw [eq_of_repC repc hr]
  exact hg

theorem c_ne : elemW cWordK ≠ 1 := ne_of repc repC_idK c_parts.2.2.2.2.1

theorem c_sq : elemW cWordK * elemW cWordK = 1 :=
  (eqB_iff (repC_pc repc repc) repC_idK).1 c_parts.2.2.2.2.2.1

theorem E_le_Q : Ek ≤ Qk := by
  rw [closure_le]
  refine of_gens (k := 3) (by decide) fun j hj => ?_
  obtain ⟨hp, he⟩ := c_parts.2.2.2.2.2.2.1 j hj
  obtain ⟨g, hg, hr⟩ := (cov_of rQ).2.2 (TKP j) (by rw [cQ]; exact hp)
  rw [he] at hr
  rw [eq_of_repC (gen_of lE hdE j hj) hr]
  exact hg

theorem E_comm : ∀ e ∈ Ek, ∀ f ∈ Ek, e * f = f * e :=
  commute_of_closure (of_gens (k := 3) (by decide) fun j hj =>
    of_gens (k := 3) (by decide) fun l hl =>
      (comm_iff (gen_of lE hdE j hj) (gen_of lE hdE l hl)).1
        (c_parts.2.2.2.2.2.2.2.1 j hj l hl))

theorem E_sq : ∀ e ∈ Ek, e * e = 1 := by
  intro e he
  obtain ⟨i, hi, hr⟩ := (cov_of rE).2.1 e he
  exact (eqB_iff (repC_pc hr hr) repC_idK).1 (c_parts.2.2.2.2.2.2.2.2 i (by rw [← cE]; exact hi))

theorem Q_cen : ∀ q ∈ Qk, (∀ r ∈ Qk, q * r = r * q) → q = 1 ∨ q = elemW cWordK := by
  intro q hq hc
  obtain ⟨i, hi, hr⟩ := (cov_of rQ).2.1 q hq
  have h := allN_spec ch26773_qc i (by rw [← cQ]; exact hi)
  unfold qCentK at h
  simp only [strictB_app, bIf26773] at h
  split_ifs at h with h1 h2 h3
  all_goals first
    | exact absurd ((comm_iff hr (gen_of lQ hdQ (TKQW i) (Nat.blt_eq.mp h1))).2
        (hc _ (elemW_getD_mem qWordsK (TKQW i)))) ‹¬commP _ _ = true›
    | exact Or.inl (eq_of_repC (by rw [← Nat.eq_of_beq_eq_true h]; exact hr) repC_idK)
    | exact Or.inr (eq_of_repC (by rw [← Nat.eq_of_beq_eq_true h]; exact hr) repc)
    | exact Or.inr (eq_of_repC (by rw [← Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 h).2]; exact hr)
        repc)

theorem Q_comm : ∀ q ∈ Qk, ∀ r ∈ Qk, q * r = r * q ∨ q * r = elemW cWordK * (r * q) := by
  intro q hq r hr
  obtain ⟨i, hi, hri⟩ := (cov_of rQ).2.1 q hq
  obtain ⟨j, hj, hrj⟩ := (cov_of rQ).2.1 r hr
  have h := allN_spec ch26773_qm i (by rw [← cQ]; exact hi)
  unfold qCommK at h
  simp only [strictB_app] at h
  have h' := allN_spec h j (by rw [← cQ]; exact hj)
  simp only [strictB_app, bIf26773] at h'
  split_ifs at h' with h1
  · exact Or.inl ((eqB_iff (repC_pc hri hrj) (repC_pc hrj hri)).1 h1)
  · exact Or.inr ((eqB_iff (repC_pc hri hrj) (repC_pc repc (repC_pc hrj hri))).1 h')

theorem Q_sq : ∀ q ∈ Qk, q * q = 1 ∨ q * q = elemW cWordK := by
  intro q hq
  obtain ⟨i, hi, hr⟩ := (cov_of rQ).2.1 q hq
  have h := allN_spec ch26773_qs i (by rw [← cQ]; exact hi)
  unfold qSqK at h
  simp only [strictB_app, bIf26773] at h
  split_ifs at h with h1
  · exact Or.inl ((eqB_iff (repC_pc hr hr) repC_idK).1 h1)
  · exact Or.inr ((eqB_iff (repC_pc hr hr) repc).1 h)

theorem repx : RepC (TKZ.GI 0) (elemW xWordK) := gen_of lZ hdZ 0 (by norm_num)
theorem repy : RepC (TKZ.GI 1) (elemW yWordK) := gen_of lZ hdZ 1 (by norm_num)

theorem zpow4_cases {M : Type*} [Group M] {x : M} (hx : orderOf x = 4) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x ∨ x ^ k = x * x ∨ x ^ k = x * x * x := by
  rw [← zpow_mod_orderOf, hx]
  obtain h | h | h | h : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨ k % ((4 : ℕ) : ℤ) = 2 ∨
      k % ((4 : ℕ) : ℤ) = 3 := by omega
  · left
    rw [h]
    simp
  · right
    left
    rw [h]
    simp
  · right
    right
    left
    rw [h]
    simp [zpow_two, pow_two]
  · right
    right
    right
    rw [h]
    simp [zpow_ofNat, pow_succ]

theorem zc_facts : orderOf (elemW xWordK) = 4 ∧ orderOf (elemW yWordK) = 2 ∧
    elemW yWordK ∉ zpowers (elemW xWordK) ∧ elemW xWordK * elemW yWordK = elemW yWordK * elemW xWordK ∧
    (∀ j < 4, elemW xWordK * elemW (qWordsK.getD j []) = elemW (qWordsK.getD j []) * elemW xWordK ∧
      elemW yWordK * elemW (qWordsK.getD j []) = elemW (qWordsK.getD j []) * elemW yWordK) := by
  have h := ch26773_zc
  simp only [strictB_app, bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  have rx := repx
  have ry := repy
  have rxx := repC_pc rx rx
  have hx2 : elemW xWordK * elemW xWordK ≠ 1 := ne_of rxx repC_idK a1
  have hx4 : (elemW xWordK * elemW xWordK) * (elemW xWordK * elemW xWordK) = 1 :=
    (eqB_iff (repC_pc rxx rxx) repC_idK).1 a2
  have hxo : orderOf (elemW xWordK) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := elemW xWordK)
      (by simpa [pow_two] using hx2) (by simpa [pow_succ, pow_two, mul_assoc] using hx4)
    simpa using this
  have hy1 : elemW yWordK ≠ 1 := ne_of ry repC_idK a3
  have hy2 : elemW yWordK * elemW yWordK = 1 := (eqB_iff (repC_pc ry ry) repC_idK).1 a4
  have hyo : orderOf (elemW yWordK) = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  refine ⟨hxo, hyo, ?_, (comm_iff rx ry).1 a8, fun j hj => ?_⟩
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rcases zpow4_cases hxo k with e | e | e | e
    · exact hy1 (by rw [← hk, e])
    · exact ne_of ry rx a5 (by rw [← hk, e])
    · exact ne_of ry rxx a6 (by rw [← hk, e])
    · exact ne_of ry (repC_pc rxx rx) a7 (by rw [← hk, e])
  · have h := allN_spec a9 j hj
    simp only [bAnd_iff] at h
    exact ⟨(comm_iff rx (gen_of lQ hdQ j hj)).1 h.1, (comm_iff ry (gen_of lQ hdQ j hj)).1 h.2⟩

end CFSG.KD.HN1408.TK

end
