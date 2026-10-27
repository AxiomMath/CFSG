module

public import Certificates.Kernel.IdxFour.M0OK
public import Certificates.Kernel.IdxFour.E0Chain
public import CFSG.Certificates.Kernel.IdxFourCosetSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4M

open CFSG.KC.IF4C CFSG.KC.IF4M CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem rowsP_MT : rowsP (look MT 0) = s12Rows ∧ rowsP (look MT 1) = s6Rows ∧
    rowsP (look MT 2) = sigRows ∧ rowsP (look MT 3) = y3Rows := by
  decide +kernel

theorem m0_spec :
    (∀ g < 4, mulP (look MT g) (look MT (g + 4)) = idP) ∧
    (∀ a < 4, mulP (look Q a) (look QI a) = idP) ∧
    look Q 0 = idP ∧ look Q 1 = look MT 0 ∧ look Q 2 = look MT 2 ∧
    look Q 3 = mulP (look MT 0) (look MT 2) ∧
    wordM MT (AW.getD 0 []) = look CFSG.KD.IF4E.SP 0 ∧ (∀ e ∈ AW.getD 0 [], e < 4) ∧
    wordM MT (AW.getD 1 []) = look CFSG.KD.IF4E.SP 1 ∧ (∀ e ∈ AW.getD 1 [], e < 4) ∧
    look MT 3 = look CFSG.KD.IF4E.SP 2 ∧
    (∀ g < 4, ∀ e < 3, pathOK CFSG.KD.IF4E.O (CJ.getD (3 * g + e) []) = true ∧
      mulP (look MT g) (mulP (look CFSG.KD.IF4E.SP e) (look MT (g + 4))) =
        pathP CFSG.KD.IF4E.T (CJ.getD (3 * g + e) [])) ∧
    (∀ g < 4, ∀ a < 4, (CS.getD (4 * g + a) []).getD 0 0 < 4 ∧
      pathOK CFSG.KD.IF4E.O (CS.getD (4 * g + a) []).tail = true ∧
      mulP (look MT g) (mulP (look Q a) (look QI ((CS.getD (4 * g + a) []).getD 0 0))) =
        pathP CFSG.KD.IF4E.T (CS.getD (4 * g + a) []).tail) ∧
    (∀ a < 4, ∀ b < 4, a ≠ b →
      ((NG.getD (4 * a + b) []).drop (2 + (NG.getD (4 * a + b) []).getD 0 0)).getD 0 0 =
        mulP (look Q a) (look QI b) ∧
      negRec CFSG.KD.IF4E.T CFSG.KD.IF4E.O CFSG.KD.IF4E.PS CFSG.KD.IF4E.B 5
        ((NG.getD (4 * a + b) []).getD 1 0) 0
        (((NG.getD (4 * a + b) []).drop 2).take ((NG.getD (4 * a + b) []).getD 0 0))
        (((NG.getD (4 * a + b) []).drop (2 + (NG.getD (4 * a + b) []).getD 0 0)).getD 0 0)
        ((NG.getD (4 * a + b) []).drop (2 + (NG.getD (4 * a + b) []).getD 0 0)).tail = true) := by
  have h := cf17600m0
  unfold m0OK at h
  simp only [Bool.and_eq_true, allBelow_iff, Nat.beq_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, fun g hg e he => h12 g hg e he,
    fun g hg a ha => ⟨(h13 g hg a ha).1.1, (h13 g hg a ha).1.2, (h13 g hg a ha).2⟩,
    fun a ha b hb hab => ?_⟩
  rcases h14 a ha b hb with h | h
  · exact absurd h hab
  · exact h

theorem exists_gen : ∀ g < 4, ∃ U ∈ M0, IsP U (look MT g) ∧ IsP U⁻¹ (look MT (g + 4)) := by
  intro g hg
  obtain ⟨U, hU⟩ := IsP.exists_of_mul (m0_spec.1 g hg)
  refine ⟨U, Subgroup.subset_closure ?_, hU, hU.inv (m0_spec.1 g hg)⟩
  obtain ⟨r0, r1, r2, r3⟩ := rowsP_MT
  interval_cases g
  · exact ⟨s12Rows, by simp [m0Gens], fun v => (hU v).trans (linP_eq_of_rowsP r0 v)⟩
  · exact ⟨s6Rows, by simp [m0Gens], fun v => (hU v).trans (linP_eq_of_rowsP r1 v)⟩
  · exact ⟨sigRows, by simp [m0Gens], fun v => (hU v).trans (linP_eq_of_rowsP r2 v)⟩
  · exact ⟨y3Rows, by simp [m0Gens], fun v => (hU v).trans (linP_eq_of_rowsP r3 v)⟩

theorem gen_isP {U : GL} (hU : U ∈ Viol.GenSet m0Gens) : ∃ g < 4, IsP U (look MT g) := by
  obtain ⟨r, hr, hU⟩ := hU
  obtain ⟨r0, r1, r2, r3⟩ := rowsP_MT
  simp only [m0Gens, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, fun v => (hU v).trans (linP_eq_of_rowsP r0 v).symm⟩
  · exact ⟨1, by omega, fun v => (hU v).trans (linP_eq_of_rowsP r1 v).symm⟩
  · exact ⟨2, by omega, fun v => (hU v).trans (linP_eq_of_rowsP r2 v).symm⟩
  · exact ⟨3, by omega, fun v => (hU v).trans (linP_eq_of_rowsP r3 v).symm⟩

theorem e0_gen_isP {U : GL} (hU : U ∈ Viol.GenSet e0Gens) :
    ∃ e < 3, IsP U (look CFSG.KD.IF4E.SP e) := by
  obtain ⟨r, hr, hU⟩ := hU
  obtain ⟨r0, r1, r2⟩ := CFSG.KD.IF4E.rowsP_gens
  simp only [e0Gens, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨0, by omega, fun v => (hU v).trans (linP_eq_of_rowsP r0 v).symm⟩
  · exact ⟨1, by omega, fun v => (hU v).trans (linP_eq_of_rowsP r1 v).symm⟩
  · exact ⟨2, by omega, fun v => (hU v).trans (linP_eq_of_rowsP r2 v).symm⟩

theorem E0_le_M0 : E0 ≤ M0 := by
  rw [E0, Viol.genGrp, Subgroup.closure_le]
  intro U hU
  obtain ⟨e, he, hUP⟩ := e0_gen_isP hU
  have hMT : ∀ g < 4, ∃ U ∈ M0, IsP U (look MT g) := fun g hg =>
    (exists_gen g hg).imp fun U h => ⟨h.1, h.2.1⟩
  obtain ⟨-, -, -, -, -, -, hw0, ha0, hw1, ha1, hy, -⟩ := m0_spec
  interval_cases e
  · obtain ⟨V, hV, hVP⟩ := exists_wordM hMT _ ha0
    rw [hw0] at hVP
    rw [hUP.inj hVP]
    exact hV
  · obtain ⟨V, hV, hVP⟩ := exists_wordM hMT _ ha1
    rw [hw1] at hVP
    rw [hUP.inj hVP]
    exact hV
  · obtain ⟨V, hV, hVP, -⟩ := exists_gen 3 (by omega)
    rw [hy] at hVP
    rw [hUP.inj hVP]
    exact hV

theorem exists_path {as : List Nat} (h : pathOK CFSG.KD.IF4E.O as = true) :
    ∃ P ∈ E0, IsP P (pathP CFSG.KD.IF4E.T as) := by
  rw [← CFSG.KD.IF4E.lvlGrp_zero_eq_E0]
  exact ChainHyp.path0 CFSG.KD.IF4E.e0ChainHyp as 0 h

theorem conj_gen_mem {g : Nat} (hg : g < 4) {U : GL} (hU : IsP U (look MT g))
    (hUi : IsP U⁻¹ (look MT (g + 4))) {x : GL} (hx : x ∈ E0) : U * x * U⁻¹ ∈ E0 := by
  rw [E0, Viol.genGrp] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨e, he, hxP⟩ := e0_gen_isP hx
    obtain ⟨hp, heq⟩ := m0_spec.2.2.2.2.2.2.2.2.2.2.2.1 g hg e he
    obtain ⟨P, hP, hPP⟩ := exists_path hp
    rw [← heq] at hPP
    rw [mul_assoc, hPP.inj (hU.mul (hxP.mul hUi)) |>.symm]
    exact hP
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : U * (x * y) * U⁻¹ = (U * x * U⁻¹) * (U * y * U⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : U * x⁻¹ * U⁻¹ = (U * x * U⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem conj_mem_E0 {m : GL} (hm : m ∈ M0) {x : GL} (hx : x ∈ E0) : m * x * m⁻¹ ∈ E0 := by
  refine mem_of_closure (K := {m | ∀ x ∈ E0, m * x * m⁻¹ ∈ E0}) ?_ ?_ hm x hx
  · intro x hx
    rwa [one_mul, inv_one, mul_one]
  · intro s hs y hy x hx
    obtain ⟨g, hg, hsP⟩ := gen_isP hs
    obtain ⟨U, -, hUP, hUi⟩ := exists_gen g hg
    rw [hsP.inj hUP]
    have : U * y * x * (U * y)⁻¹ = U * (y * x * y⁻¹) * U⁻¹ := by group
    rw [this]
    exact conj_gen_mem hg hUP hUi (hy x hx)

theorem exists_q : ∀ a < 4, ∃ U ∈ M0, IsP U (look Q a) ∧ IsP U⁻¹ (look QI a) := by
  obtain ⟨-, h2, h3, h4, h5, h6, -⟩ := m0_spec
  obtain ⟨G0, hG0, hG0P, -⟩ := exists_gen 0 (by omega)
  obtain ⟨G2, hG2, hG2P, -⟩ := exists_gen 2 (by omega)
  intro a ha
  have key : ∃ U ∈ M0, IsP U (look Q a) := by
    interval_cases a
    · exact ⟨1, Subgroup.one_mem _, h3 ▸ IsP.one⟩
    · exact ⟨G0, hG0, h4 ▸ hG0P⟩
    · exact ⟨G2, hG2, h5 ▸ hG2P⟩
    · exact ⟨G0 * G2, Subgroup.mul_mem _ hG0 hG2, h6 ▸ hG0P.mul hG2P⟩
  obtain ⟨U, hU, hUP⟩ := key
  exact ⟨U, hU, hUP, hUP.inv (h2 a ha)⟩

theorem card_M0 : Nat.card M0 = 39191040 := by
  choose! qE hqM hqP hqI using exists_q
  have hq0 : qE 0 = 1 := (hqP 0 (by omega)).inj (m0_spec.2.2.1 ▸ IsP.one)
  have hsurj : ∀ m ∈ M0, ∃ e ∈ E0, ∃ a < 4, m = e * qE a := by
    intro m hm
    refine mem_of_closure (K := {m | ∃ e ∈ E0, ∃ a < 4, m = e * qE a}) ?_ ?_ hm
    · exact ⟨1, Subgroup.one_mem _, 0, by omega, by rw [hq0, mul_one]⟩
    · rintro s hs y ⟨e, he, a, ha, rfl⟩
      obtain ⟨g, hg, hsP⟩ := gen_isP hs
      obtain ⟨U, hUM, hUP, hUi⟩ := exists_gen g hg
      rw [hsP.inj hUP]
      obtain ⟨hb, hp, heq⟩ := m0_spec.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg a ha
      set b := (CS.getD (4 * g + a) []).getD 0 0
      obtain ⟨P, hP, hPP⟩ := exists_path hp
      rw [← heq] at hPP
      have hPe : P = U * (qE a * (qE b)⁻¹) := hPP.inj (hUP.mul ((hqP a ha).mul (hqI b hb)))
      refine ⟨U * e * U⁻¹ * P, Subgroup.mul_mem _ (conj_mem_E0 hUM he) hP, b, hb, ?_⟩
      rw [hPe]
      group
  have hdist : ∀ a < 4, ∀ b < 4, qE a * (qE b)⁻¹ ∈ E0 → a = b := by
    intro a ha b hb hmem
    by_contra hab
    obtain ⟨h0, hneg⟩ := m0_spec.2.2.2.2.2.2.2.2.2.2.2.2.2 a ha b hb hab
    have hX : IsP (qE a * (qE b)⁻¹) _ := (hqP a ha).mul (hqI b hb)
    rw [← h0] at hX
    rw [← CFSG.KD.IF4E.lvlGrp_zero_eq_E0] at hmem
    exact ChainHyp.not_mem_of_negRec CFSG.KD.IF4E.e0ChainHyp _ 0 _ _ _ (by omega) hmem hX hneg
  let φ : E0 × Fin 4 → M0 := fun p =>
    ⟨p.1 * qE p.2, Subgroup.mul_mem _ (E0_le_M0 p.1.2) (hqM _ p.2.2)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨e, a⟩ ⟨e', b⟩ h
      have h' : (e : GL) * qE a = e' * qE b := congrArg Subtype.val h
      have hm : qE a * (qE b)⁻¹ = (e : GL)⁻¹ * e' := by
        calc qE a * (qE b)⁻¹ = (e : GL)⁻¹ * (e * qE a) * (qE b)⁻¹ := by group
          _ = (e : GL)⁻¹ * e' := by rw [h']; group
      have hab : (a : Nat) = b :=
        hdist a a.2 b b.2 (hm ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ e.2) e'.2)
      have hab' : a = b := Fin.ext hab
      subst hab'
      exact Prod.ext (Subtype.ext (mul_right_cancel h')) rfl
    · rintro ⟨m, hm⟩
      obtain ⟨e, he, a, ha, rfl⟩ := hsurj m hm
      exact ⟨(⟨e, he⟩, ⟨a, ha⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective φ hφ, Nat.card_prod, CFSG.KD.IF4E.card_E0,
    Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

end CFSG.KD.IF4M

end
