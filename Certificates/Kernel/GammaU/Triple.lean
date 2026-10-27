
module

public import Certificates.Kernel.GammaU.TripleOK
public import Certificates.Kernel.GammaU.CensusConf
public import Certificates.Kernel.GammaU.SigmaFactsBase
public import CFSG.Certificates.Kernel.GammaUViolSound
public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairBase

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUTB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
  exact h

theorem linOfRows_theta0R' (x : V12) : linOfRows theta0R x = theta0 x := by
  have h : ∀ j : Fin 12, appN theta0R (2 ^ (j : ℕ)) = theta0N (2 ^ (j : ℕ)) := by decide
  have hfun : linOfRows theta0R = theta0 := linMap_ext fun j => by
    rw [← vecOf_appN, h j, vecOf_theta0N (two_pow_lt j)]
  rw [hfun]

theorem linP_TH (v : V12) : linP CFSG.KD.GUC0.TH v = theta0 v := by
  rw [← CFSG.KD.GUC0.isP_θA v, (CFSG.KD.GUCB.isP_TH_iff _).1 CFSG.KD.GUC0.isP_θA v,
    linOfRows_theta0R']

theorem forall₂_of_getD {P : List Nat} {gs : List (Array ℕ)} (hl : P.length = gs.length)
    (h : ∀ l < gs.length, ∀ v, linP (P.getD l 0) v = linOfRows (gs.getD l #[]) v) :
    List.Forall₂ (fun p g => ∀ v, linP p v = linOfRows g v) P gs := by
  induction gs generalizing P with
  | nil =>
    cases P with
    | nil => exact .nil
    | cons => simp at hl
  | cons g gs ih =>
    cases P with
    | nil => simp at hl
    | cons p P =>
      exact .cons (h 0 (by simp)) (ih (by simpa using hl) fun l hl' => h (l + 1) (by simpa using hl'))

theorem getD_five (CG c : Nat) {l : Nat} (hl : l < 5) : (five CG c).getD l 0 = look CG (5 * c + l) := by
  interval_cases l <;> rfl

theorem compOf_iff {c : Nat} (hc : c < 32) :
    (∀ m, ∃ x ∈ compOf c, ∀ v, linOfRows x v = linP (subQ (five CFSG.KD.GUC0.CG c) m) v) ∧
      ∀ x ∈ compOf c, ∃ m < 32, ∀ v, linOfRows x v = linP (subQ (five CFSG.KD.GUC0.CG c) m) v := by
  have h := mem_subsetProducts_iff (forall₂_of_getD (P := five CFSG.KD.GUC0.CG c)
    (gs := ResPair.compGens c) (by rw [CFSG.KD.GUCB.length_compGens]; rfl) fun l hl v => by
      rw [CFSG.KD.GUCB.length_compGens] at hl
      rw [getD_five _ _ hl]
      exact CFSG.KD.GUCB.linP_cg hc hl v)
  rw [CFSG.KD.GUCB.length_compGens] at h
  exact h

theorem letT_mem {i : Nat} {CG FT FTi FC TH X : Nat} {T : Nat → GL} {θ C : GL} {N2 : List Nat}
    {NN CC CCi : Nat} (hcg : ∀ c < 32, ∀ g ∈ five CG c, ∃ U, IsP U g) (hi : i < 32)
    (hX : fld FC X < 32) (hT : IsP (T X) (look FT X)) (hTi : IsP (T X)⁻¹ (look FTi X))
    (hθ : IsP θ TH) (hN : ∀ e < NN, ∃ U ∈ ResPair.n2 i, IsP U (nthD 0 N2 e))
    (hC : IsP C CC) (hCi : IsP C⁻¹ CCi) :
    ∀ e < NN + 11, ∃ U ∈ ResPair.n2 i ⊔ (confR CG FC i T θ X).map (MulAut.conj C).toMonoidHom,
      IsP U (letT N2 NN (candL CG FT FTi FC TH i X) CC CCi e) := by
  intro e he
  unfold letT
  by_cases hlt : e < NN
  · rw [blt_true hlt, cond_true]
    obtain ⟨U, hU, hUP⟩ := hN e hlt
    exact ⟨U, Subgroup.mem_sup_left hU, hUP⟩
  · rw [blt_false hlt, cond_false]
    set l := e - NN with hl
    have hl11 : l < 11 := by omega
    have hV : ∃ V ∈ confR CG FC i T θ X, IsP V (candL CG FT FTi FC TH i X l) := by
      unfold candL confR candR
      by_cases h5 : l < 5
      · rw [blt_true h5, cond_true]
        obtain ⟨U, hU⟩ := hcg i hi _ (mem_five.2 ⟨l, h5, rfl⟩)
        exact ⟨U, Subgroup.subset_closure (Or.inl (Or.inl
          (Subgroup.subset_closure ⟨_, mem_five.2 ⟨l, h5, rfl⟩, hU⟩))), hU⟩
      · rw [blt_false h5, cond_false]
        by_cases h10 : l < 10
        · rw [blt_true h10, cond_true]
          have hm : look CG (Nat.add (Nat.mul 5 (fld FC X)) (Nat.sub l 5)) ∈ five CG (fld FC X) :=
            mem_five.2 ⟨l - 5, by omega, rfl⟩
          obtain ⟨U, hU⟩ := hcg _ hX _ hm
          refine ⟨T X * U * (T X)⁻¹, Subgroup.subset_closure (Or.inl (Or.inr
            ⟨U, Subgroup.subset_closure ⟨_, hm, hU⟩, rfl⟩)), ?_⟩
          rw [mul_assoc]
          exact hT.mul (hU.mul hTi)
        · rw [blt_false h10, cond_false]
          exact ⟨θ, Subgroup.subset_closure (Or.inr rfl), hθ⟩
    obtain ⟨V, hV, hVP⟩ := hV
    refine ⟨C * V * C⁻¹, Subgroup.mem_sup_right ⟨V, hV, rfl⟩, ?_⟩
    rw [mul_assoc]
    exact hC.mul (hVP.mul hCi)

theorem isP_wordP {NLG NLGI : Nat} (hinv : invOK NLG NLGI 3 = true) (w : List Nat)
    (hw : ltAll 6 w = true) : ∃ U ∈ lGrp NLG 3, IsP U (wordP NLG NLGI w) := by
  have hl := invOK_spec _ _ hinv
  refine isP_wordF (n := 6) (fun e he => ?_) w hw
  have hl3 : e / 2 < 3 := by omega
  obtain ⟨U, hU⟩ := IsP.exists_of_mul (hl _ hl3)
  have hm : U ∈ lGrp NLG 3 := Subgroup.subset_closure ⟨_, hl3, hU⟩
  cases h : Nat.beq (e % 2) 0
  · exact ⟨U⁻¹, inv_mem hm, by rw [cond_false]; exact hU.inv (hl _ hl3)⟩
  · exact ⟨U, hm, by rw [cond_true]; exact hU⟩

theorem n2_isP {i : Nat} {NI : Nat} (hrows : ((ResPair.n2Gens i).all fun r => rowsOK r.toList) = true)
    (hinv : invsOK ((ResPair.n2Gens i).map packR) NI = true) :
    ∀ e < (ResPair.n2Gens i).length, ∃ U ∈ ResPair.n2 i,
      IsP U (nthD 0 ((ResPair.n2Gens i).map packR) e) := by
  intro e he
  have hl : e < ((ResPair.n2Gens i).map packR).length := by rw [List.length_map]; exact he
  obtain ⟨U, hU⟩ := IsP.exists_of_mul (invsOK_spec hinv e hl).1
  rw [nthD_map _ _ _ #[] he] at hU ⊢
  have hmem : (ResPair.n2Gens i).getD e #[] ∈ ResPair.n2Gens i := by
    rw [getD_of_lt _ he]
    exact List.getElem_mem he
  have hr : rowsOK ((ResPair.n2Gens i).getD e #[]).toList = true :=
    List.all_eq_true.1 hrows _ hmem
  exact ⟨U, Subgroup.subset_closure ⟨_, hmem, (isP_packR hr U).1 hU⟩, hU⟩

end CFSG.KD.GUTB

namespace CFSG.KD.GUT0

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS CFSG.KD.GUTB
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem lists_spec : UM.length = 12 ∧ XA.length = 12 ∧ (∀ X ∈ XA, X < 384) ∧
    WT.length = 144 ∧ NN = N2.length ∧
    (∀ m < 32, unitP CFSG.KD.GUC0.TH (subQ L m) = true → m = 0 ∨ m ∈ UM ∨ m ∈ HM) ∧
    ∀ X < 384, fld CFSG.KD.GUC0.LB X = CFSG.KD.GUC0.AR → X ∈ XA := by
  have h := ct16966a_lists
  unfold lists at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, ltAll_iff, allBelow_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun m hm hu => ?_, fun X hX hl => ?_⟩
  · have := h6 m hm
    simp only [Bool.or_eq_true, Bool.not_eq_true', hu, Nat.beq_eq, memN_iff] at this
    rcases this with ((h | h) | h) | h
    · exact absurd h (by simp)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · have := h7 X hX
    simp only [Bool.or_eq_true, Bool.not_eq_true', memN_iff] at this
    rcases this with h | h
    · exact absurd hl (Nat.ne_of_beq_eq_false h)
    · exact h

theorem ar_mem {X : Nat} (hX : X < 384) (hl : fld CFSG.KD.GUC0.LB X = CFSG.KD.GUC0.AR) :
    X ∈ XA := lists_spec.2.2.2.2.2.2 X hX hl

theorem hm_eq : HM.map (subQ L) = (ResPair.hyp10 0).map packR := ct16966a_h10

theorem triple_s0 {x q : Nat} (hx : x < 12) (hq : q < 12) :
    ∃ C : GL, IsP C (look CC q) ∧ IsP C⁻¹ (look CCi q) ∧ C ∈ lGrp NLG 3 ∧
      mulP (subQ L (nthD 0 UM q)) (look CC q) = mulP (look CC q) CFSG.KD.GUC0.S0 ∧
      Viol.Violation (ResPair.n2 0 ⊔ (confR CFSG.KD.GUC0.CG CFSG.KD.GUC0.FC 0 CFSG.KD.GUC0.TX
        CFSG.KD.GUC0.θA (nthD 0 XA x)).map (MulAut.conj C).toMonoidHom) (compOf 0) (compOf 0) := by
  obtain ⟨-, hXA, hX384, -, hNN, -, -⟩ := lists_spec
  have hcj := (allBelow_iff _ _).1 ct16966a_cj q hq
  unfold cj at hcj
  simp only [Bool.and_eq_true, Nat.beq_eq] at hcj
  obtain ⟨⟨⟨hw, hCW⟩, hCWI⟩, hcjOK⟩ := hcj
  obtain ⟨C, hCm, hC⟩ := isP_wordP ct16966a_inv _ hw
  rw [hCW] at hC
  have hcjOK' := hcjOK
  unfold CFSG.KC.GUV.cjOK at hcjOK'
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hcjOK'
  have hCi : IsP C⁻¹ (look CCi q) := hC.inv hcjOK'.1
  have hXmem : nthD 0 XA x ∈ XA := nthD_mem 0 (by rw [hXA]; exact hx)
  have hX : nthD 0 XA x < 384 := hX384 _ hXmem
  have hN : ∀ e < NN, ∃ U ∈ ResPair.n2 0, IsP U (nthD 0 N2 e) := by
    intro e he
    rw [ct16966a_n2]
    refine n2_isP CFSG.KD.GUS0.cs16981a_rows CFSG.KD.GUS0.cs16981a_inv e ?_
    rw [hNN, ct16966a_n2, List.length_map] at he
    exact he
  refine ⟨C, hC, hCi, hCm, hcjOK'.2, ?_⟩
  have hd := (allBelow_iff _ _).1 (ct16966a_all x hx) q hq
  unfold tri let0 at hd
  exact d2aOK_spec hd (letT_mem CFSG.KD.GUCB.exists_isP_cg (by norm_num)
    (CFSG.KD.GUC0.len_spec.2.2.2 _ hX) (CFSG.KD.GUC0.isP_TX hX)
    ((CFSG.KD.GUC0.isP_TX hX).inv (CFSG.KD.GUC0.inv_spec.1 _ hX)) CFSG.KD.GUC0.isP_θA hN hC hCi)
    linP_TH (compOf_iff (by norm_num)).1

end CFSG.KD.GUT0

namespace CFSG.KD.GUT1

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV CFSG.KC.GUS CFSG.KD.GUTB
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem lists_spec : UM.length = 12 ∧ XA.length = 4 ∧ (∀ X ∈ XA, X < 384) ∧
    WT.length = 48 ∧ NN = N2.length ∧
    (∀ m < 32, unitP CFSG.KD.GUC1.TH (subQ L m) = true → m = 0 ∨ m ∈ UM ∨ m ∈ HM) ∧
    ∀ X < 384, fld CFSG.KD.GUC1.LB X = CFSG.KD.GUC1.AR → X ∈ XA := by
  have h := ct16966b_lists
  unfold lists at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq, ltAll_iff, allBelow_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun m hm hu => ?_, fun X hX hl => ?_⟩
  · have := h6 m hm
    simp only [Bool.or_eq_true, Bool.not_eq_true', hu, Nat.beq_eq, memN_iff] at this
    rcases this with ((h | h) | h) | h
    · exact absurd h (by simp)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · have := h7 X hX
    simp only [Bool.or_eq_true, Bool.not_eq_true', memN_iff] at this
    rcases this with h | h
    · exact absurd hl (Nat.ne_of_beq_eq_false h)
    · exact h

theorem ar_mem {X : Nat} (hX : X < 384) (hl : fld CFSG.KD.GUC1.LB X = CFSG.KD.GUC1.AR) :
    X ∈ XA := lists_spec.2.2.2.2.2.2 X hX hl

theorem hm_eq : HM.map (subQ L) = (ResPair.hyp10 1).map packR := ct16966b_h10

theorem triple_s0 {x q : Nat} (hx : x < 4) (hq : q < 12) :
    ∃ C : GL, IsP C (look CC q) ∧ IsP C⁻¹ (look CCi q) ∧ C ∈ lGrp NLG 3 ∧
      mulP (subQ L (nthD 0 UM q)) (look CC q) = mulP (look CC q) CFSG.KD.GUC1.S0 ∧
      Viol.Violation (ResPair.n2 1 ⊔ (confR CFSG.KD.GUC1.CG CFSG.KD.GUC1.FC 1 CFSG.KD.GUC1.TX
        CFSG.KD.GUC1.θA (nthD 0 XA x)).map (MulAut.conj C).toMonoidHom) (compOf 1) (compOf 1) := by
  obtain ⟨-, hXA, hX384, -, hNN, -, -⟩ := lists_spec
  have hcj := (allBelow_iff _ _).1 ct16966b_cj q hq
  unfold cj at hcj
  simp only [Bool.and_eq_true, Nat.beq_eq] at hcj
  obtain ⟨⟨⟨hw, hCW⟩, hCWI⟩, hcjOK⟩ := hcj
  obtain ⟨C, hCm, hC⟩ := isP_wordP ct16966b_inv _ hw
  rw [hCW] at hC
  have hcjOK' := hcjOK
  unfold CFSG.KC.GUV.cjOK at hcjOK'
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hcjOK'
  have hCi : IsP C⁻¹ (look CCi q) := hC.inv hcjOK'.1
  have hXmem : nthD 0 XA x ∈ XA := nthD_mem 0 (by rw [hXA]; exact hx)
  have hX : nthD 0 XA x < 384 := hX384 _ hXmem
  have hN : ∀ e < NN, ∃ U ∈ ResPair.n2 1, IsP U (nthD 0 N2 e) := by
    intro e he
    rw [ct16966b_n2]
    refine n2_isP CFSG.KD.GUS1.cs16981b_rows CFSG.KD.GUS1.cs16981b_inv e ?_
    rw [hNN, ct16966b_n2, List.length_map] at he
    exact he
  have hTH : ∀ v, linP CFSG.KD.GUC1.TH v = theta0 v := by
    rw [CFSG.KD.GUC1.cg_eq.2]
    exact linP_TH
  have hL : ∀ m, ∃ x ∈ compOf 1, ∀ v, linOfRows x v = linP (subQ L m) v := by
    unfold L
    rw [CFSG.KD.GUC1.cg_eq.1]
    exact (compOf_iff (by norm_num)).1
  refine ⟨C, hC, hCi, hCm, hcjOK'.2, ?_⟩
  have hd := (allBelow_iff _ _).1 (ct16966b_all x hx) q hq
  unfold tri let1 at hd
  exact d2aOK_spec hd (letT_mem CFSG.KD.GUC1.exists_isP_cg (by norm_num)
    (CFSG.KD.GUC1.len_spec.2.2.2 _ hX) (CFSG.KD.GUC1.isP_TX hX)
    ((CFSG.KD.GUC1.isP_TX hX).inv (CFSG.KD.GUC1.inv_spec.1 _ hX)) CFSG.KD.GUC1.isP_θA hN hC hCi)
    hTH hL

end CFSG.KD.GUT1

end
