
module

public import Certificates.Kernel.GammaU.BaseBridge
public import Certificates.Kernel.GammaU.Norm

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUBB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem inv_ok {c : Array ℕ} (hc : rowsOK c.toList = true)
    (hU : ∃ U : GL, ∀ v, U v = linOfRows c v) :
    mulR c (Viol.invR c) = idR ∧ mulR (Viol.invR c) c = idR := by
  obtain ⟨hlen, hlt⟩ := rowsOK_spec hc
  have hlt' : ∀ x ∈ c, x < 4096 := fun x hx => hlt x (by simpa using hx)
  have hsz : c.size = 12 := by simpa using hlen
  obtain ⟨U, hU⟩ := hU
  have hinv := linOfRows_invR hlt' hU
  have hisz : (Viol.invR c).size = 12 := by simp [Viol.invR]
  have hilt : ∀ x ∈ Viol.invR c, x < 4096 := by
    intro x hx
    simp only [Viol.invR, List.mem_toArray, List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    cases hf : List.find? (fun n => appN c n == 2 ^ j) (List.range 4096) with
    | none => simp
    | some n =>
      have := List.mem_of_find?_eq_some hf
      rw [List.mem_range] at this
      simpa using this
  have hidlt : ∀ x ∈ idR, x < 4096 := by decide
  refine ⟨rows_eq (by simp [mulR, hisz]) rfl (fun x hx => ?_) hidlt fun x => ?_,
    rows_eq (by simp [mulR, hsz]) rfl (fun x hx => ?_) hidlt fun x => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Array.mem_map.1 hx
    exact appN_lt hlt' y
  · rw [linOfRows_mulR, hinv, ← hU, apply_inv_apply, linOfRows_idR]
  · obtain ⟨y, -, rfl⟩ := Array.mem_map.1 hx
    exact appN_lt hilt y
  · rw [linOfRows_mulR, ← hU, hinv, inv_apply_apply, linOfRows_idR]

theorem resGrp_map {i : Nat} {RC RCI : List Nat} (hrc : RC = (ResPair.resConj i).map packR)
    (hrows : ((ResPair.resConj i).all fun r => rowsOK r.toList) = true)
    (hlen : lenN RC = 30) (hinv : ∀ c < 30, mulP (nthD 0 RC c) (nthD 0 RCI c) = idP)
    {U : GL} (hU : CFSG.KD.GUNB.ResP (ResPair.n2 i) RC U) {N : Subgroup GL} (hN : ResGrp i N) :
    ResGrp i (N.map (MulAut.conj U).toMonoidHom) := by
  have hl : (ResPair.resConj i).length = 30 := by
    rw [lenN_eq, hrc, List.length_map] at hlen
    exact hlen
  have hisP : ∀ k (hk : k < (ResPair.resConj i).length) (A : GL),
      (∀ v, A v = linOfRows (ResPair.resConj i)[k] v) → IsP A (nthD 0 RC k) := by
    intro k hk A hA
    rw [hrc, nthD_map _ _ _ #[] hk, getD_of_lt _ hk]
    exact (isP_packR (List.all_eq_true.1 hrows _ (List.getElem_mem hk)) A).2 hA
  obtain ⟨c, hc, h1, h2, rfl⟩ := hN
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨j', hj', hres⟩ := hU j (by omega)
  have hj'' : j' < (ResPair.resConj i).length := by omega
  have hm' := List.getElem_mem hj''
  have hex : ∃ A : GL, ∀ v, A v = linOfRows (ResPair.resConj i)[j'] v := by
    obtain ⟨A, hA⟩ := IsP.exists_of_mul (hinv j' hj')
    refine ⟨A, ?_⟩
    rw [hrc, nthD_map _ _ _ #[] hj'', getD_of_lt _ hj''] at hA
    exact (isP_packR (List.all_eq_true.1 hrows _ hm') A).1 hA
  obtain ⟨h1', h2'⟩ := inv_ok (List.all_eq_true.1 hrows _ hm') hex
  refine ⟨_, hm', h1', h2', ?_⟩
  rw [CFSG.KD.GUNB.map_conj_mul]
  exact hres _ _ (hisP j hj _ fun v => rfl) (hisP j' hj'' _ fun v => rfl)

theorem resGrp_of {i : Nat} (hrows : ((ResPair.resConj i).all fun r => rowsOK r.toList) = true)
    {j : Nat} (hj : j < (ResPair.resConj i).length) {V : GL}
    (hV : ∀ v, V v = linOfRows ((ResPair.resConj i).getD j #[]) v) {N : Subgroup GL}
    (hN : N = (ResPair.n2 i).map (MulAut.conj V).toMonoidHom) : ResGrp i N := by
  rw [getD_of_lt _ hj] at hV
  have hm := List.getElem_mem hj
  obtain ⟨h1, h2⟩ := inv_ok (List.all_eq_true.1 hrows _ hm) ⟨V, hV⟩
  refine ⟨_, hm, h1, h2, ?_⟩
  have hVe : Viol.eqvOf _ _ h1 h2 = V := LinearEquiv.ext fun v => (hV v).symm
  rw [hVe]
  exact hN

theorem rowsConj_mul {U C : GL} {a p c s0 : Nat} (hUa : ∀ v, linP a (U v) = U (linP p v))
    (hC : IsP C c) (h : mulP p c = mulP c s0) : RowsConj (U * C) (rowsP a) (rowsP s0) := by
  intro y
  have e := congrArg (fun m => linP m y) h
  simp only [linP_mulP] at e
  change linP s0 y = (U * C)⁻¹ (linP a ((U * C) y))
  rw [LinearEquiv.mul_apply, hUa, hC y, e, ← hC]
  exact (inv_apply_apply (U * C) (linP s0 y)).symm

theorem ch16968a_um : ∀ r ∈ unitaryElts 0, ∃ a < 32, a ≠ 0 ∧
    unitP CFSG.KD.GUC0.TH (subQ CFSG.KD.GUT0.L a) = true ∧ rowsP (subQ CFSG.KD.GUT0.L a) = r := by
  decide +kernel

theorem ch16968b_um : ∀ r ∈ unitaryElts 1, ∃ a < 32, a ≠ 0 ∧
    unitP CFSG.KD.GUC1.TH (subQ CFSG.KD.GUT1.L a) = true ∧ rowsP (subQ CFSG.KD.GUT1.L a) = r := by
  decide +kernel

theorem nlMem0 {U : GL} (hU : U ∈ lGrp CFSG.KD.GUT0.NLG 3) : NLMem 0 U :=
  let ⟨h1, h2, h3, h4⟩ := CFSG.KD.GUN0.nl_mem hU
  ⟨h1, h2, h3, h4⟩

theorem nlMem1 {U : GL} (hU : U ∈ lGrp CFSG.KD.GUT1.NLG 3) : NLMem 1 U :=
  let ⟨h1, h2, h3, h4⟩ := CFSG.KD.GUN1.nl_mem hU
  ⟨h1, h2, h3, h4⟩

theorem pairFacts0 : PairFacts 0 := by
  obtain ⟨-, -, -, hlen, hinv⟩ := CFSG.KD.GUN0.lists_spec
  refine ⟨_, TD, 108, te0, ⟨CFSG.KD.GUSB.s0_mem_0, frameTr, colTr0⟩,
    fun r₁ hr₁ r₂ hr₂ hne => ?_⟩
  obtain ⟨a, ha, ha0, hua, rfl⟩ := ch16968a_um r₁ hr₁
  obtain ⟨b, hb, hb0, hub, rfl⟩ := ch16968a_um r₂ hr₂
  have hab : a ≠ b := fun h => hne (by rw [h])
  obtain ⟨k, hk, U, hUm, hUa, hUb⟩ := CFSG.KD.GUN0.cover ha hb ha0 hb0 hab hua hub
  obtain ⟨C₁, C₂, hC₁, hC₂, hC₁m, hC₂m, hs₁, hs₂, -⟩ :=
    CFSG.KD.GUP0.pair_s0 hk (x₁ := 0) (x₂ := 0) (by norm_num) (by norm_num)
  refine ⟨U, C₁, C₂, nlMem0 hUm, fun N hN => resGrp_map CFSG.KD.GUP0.cp16966a_rc
    CFSG.KD.GUP0.cp16966a_rcrows hlen hinv (CFSG.KD.GUN0.res_perm U hUm) hN,
    nlMem0 hC₁m, nlMem0 hC₂m, rowsConj_mul hUa hC₁ hs₁, rowsConj_mul hUb hC₂ hs₂,
    cfgAll0 fun X₁ hX₁ hl₁ => cfgAll0 fun X₂ hX₂ hl₂ => ?_⟩
  obtain ⟨x₁, hx₁, rfl⟩ := List.getElem_of_mem (CFSG.KD.GUT0.ar_mem hX₁ hl₁)
  obtain ⟨x₂, hx₂, rfl⟩ := List.getElem_of_mem (CFSG.KD.GUT0.ar_mem hX₂ hl₂)
  have hx₁' : x₁ < 12 := by rw [← CFSG.KD.GUT0.lists_spec.2.1]; exact hx₁
  have hx₂' : x₂ < 12 := by rw [← CFSG.KD.GUT0.lists_spec.2.1]; exact hx₂
  obtain ⟨C₁', C₂', hC₁', hC₂', -, -, -, -, hP⟩ := CFSG.KD.GUP0.pair_s0 hk hx₁' hx₂'
  rw [IsP.inj hC₁' hC₁, IsP.inj hC₂' hC₂, nthD_eq, nthD_eq, List.getD_eq_getElem _ _ hx₁,
    List.getD_eq_getElem _ _ hx₂] at hP
  rcases hP with hv | ⟨j, hj, V, hV, heq⟩
  · exact Or.inl hv
  · exact Or.inr (resGrp_of CFSG.KD.GUP0.cp16966a_rcrows hj hV heq)

theorem pairFacts1 : PairFacts 1 := by
  obtain ⟨-, -, -, hlen, hinv⟩ := CFSG.KD.GUN1.lists_spec
  refine ⟨_, TD, 108, te0, ⟨CFSG.KD.GUSB.s0_mem_1, frameTr, colTr1⟩,
    fun r₁ hr₁ r₂ hr₂ hne => ?_⟩
  obtain ⟨a, ha, ha0, hua, rfl⟩ := ch16968b_um r₁ hr₁
  obtain ⟨b, hb, hb0, hub, rfl⟩ := ch16968b_um r₂ hr₂
  have hab : a ≠ b := fun h => hne (by rw [h])
  obtain ⟨k, hk, U, hUm, hUa, hUb⟩ := CFSG.KD.GUN1.cover ha hb ha0 hb0 hab hua hub
  obtain ⟨C₁, C₂, hC₁, hC₂, hC₁m, hC₂m, hs₁, hs₂, -⟩ :=
    CFSG.KD.GUP1.pair_s0 hk (x₁ := 0) (x₂ := 0) (by norm_num) (by norm_num)
  refine ⟨U, C₁, C₂, nlMem1 hUm, fun N hN => resGrp_map CFSG.KD.GUP1.cp16966b_rc
    CFSG.KD.GUP1.cp16966b_rcrows hlen hinv (CFSG.KD.GUN1.res_perm U hUm) hN,
    nlMem1 hC₁m, nlMem1 hC₂m, rowsConj_mul hUa hC₁ hs₁, rowsConj_mul hUb hC₂ hs₂,
    cfgAll1 fun X₁ hX₁ hl₁ => cfgAll1 fun X₂ hX₂ hl₂ => ?_⟩
  obtain ⟨x₁, hx₁, rfl⟩ := List.getElem_of_mem (CFSG.KD.GUT1.ar_mem hX₁ hl₁)
  obtain ⟨x₂, hx₂, rfl⟩ := List.getElem_of_mem (CFSG.KD.GUT1.ar_mem hX₂ hl₂)
  have hx₁' : x₁ < 4 := by rw [← CFSG.KD.GUT1.lists_spec.2.1]; exact hx₁
  have hx₂' : x₂ < 4 := by rw [← CFSG.KD.GUT1.lists_spec.2.1]; exact hx₂
  obtain ⟨C₁', C₂', hC₁', hC₂', -, -, -, -, hP⟩ := CFSG.KD.GUP1.pair_s0 hk hx₁' hx₂'
  rw [IsP.inj hC₁' hC₁, IsP.inj hC₂' hC₂, nthD_eq, nthD_eq, List.getD_eq_getElem _ _ hx₁,
    List.getD_eq_getElem _ _ hx₂] at hP
  rcases hP with hv | ⟨j, hj, V, hV, heq⟩
  · exact Or.inl hv
  · exact Or.inr (resGrp_of CFSG.KD.GUP1.cp16966b_rcrows hj hV heq)

theorem pairFacts : ∀ i, i = 0 ∨ i = 1 → PairFacts i := by
  rintro i (rfl | rfl)
  · exact pairFacts0
  · exact pairFacts1

end CFSG.KD.GUBB

end
