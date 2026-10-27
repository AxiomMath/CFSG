module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDenseP.ReplayN
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.M13.MonoAll
public import CFSG.Certificates.Kernel.KDenseP.M13.C16958
public import CFSG.Certificates.Kernel.KDenseP.M13.C16959
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.D13Core
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenFusion
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.HeisModel
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.Kernel.KDenseP.M13.MonoEChk0
public import CFSG.Certificates.Kernel.KDenseP.M13.MonoEChk1
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP.M13

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.M13
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.TwoPoint CFSG.Monster
  CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13
  CFSG.AGLEmbedding.Norton.MON11_13 CFSG.AGLEmbedding.Norton.MON11_13.HeisModel
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.M13M.MT = true := by
  kd_monoTabL CFSG.KD.M13ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.M13M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

open Lean in
macro "kd_m13% " pre:ident eqs:term:max nes:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(tp3B_sound CertificateChecks.KernelKDenseP.M13.data_ok $eqs $nes (by quickRfl)
      (S := rlS $(n "rn") $(n "CH") $(n "PRf") CFSG.KD.KDF.I 3) (fun x hx => rlS_lt hx)
      (CH := $(n "CH")) (nch := kd_count% $pre $(mkIdent `CH)) (IT := $(n "IT"))
      (replay_sound (run := $(n "rn")) (chk := CFSG.KD.M13.chkP (tri $eqs $nes))
        (fun S S' c h3 h4 => CFSG.KC.KDenseP.chunkOKN_loc S S' c h3 h4)
        (fun S c h => CFSG.KC.KDenseP.chunkOKN_prod S c h)
        (CH := $(n "CH")) (PR := $(n "PRf")) (GK := $(n "GKf")) (G := $(n "Gf"))
        (S0 := CFSG.KD.KDF.I) (w := 3) (ng := kd_count% $pre $(mkIdent `u))
        (by kd_allE $pre $(mkIdent `u)) (by quickRfl))
      (by quickRfl) (by quickRfl))

theorem c16958 : agreeAll e16958 = true :=
  (tp3B_sound CertificateChecks.KernelKDenseP.M13.data_ok e16958 [] (by quickRfl)
      (S := rlS CFSG.KD.M13.c16958.rn CFSG.KD.M13.c16958.CH CFSG.KD.M13.c16958.PRf
        CFSG.KD.M13.c16958.S0 27)
      (fun x hx => (rlS_lt (Nat.lt_of_lt_of_le hx (by decide))).trans (by interval_cases x <;> rfl))
      (CH := CFSG.KD.M13.c16958.CH) (nch := kd_count% CFSG.KD.M13.c16958 CH)
      (IT := CFSG.KD.M13.c16958.IT)
      (replay_sound (run := CFSG.KD.M13.c16958.rn) (chk := CFSG.KD.M13.chkP (tri e16958 []))
        (fun S S' c h3 h4 => CFSG.KC.KDenseP.chunkOKN_loc S S' c h3 h4)
        (fun S c h => CFSG.KC.KDenseP.chunkOKN_prod S c h)
        (CH := CFSG.KD.M13.c16958.CH) (PR := CFSG.KD.M13.c16958.PRf) (GK := CFSG.KD.M13.c16958.GKf)
        (G := CFSG.KD.M13.c16958.Gf) (S0 := CFSG.KD.M13.c16958.S0) (w := 27)
        (ng := kd_count% CFSG.KD.M13.c16958 u) (by kd_allE CFSG.KD.M13.c16958 u) (by quickRfl))
      (by quickRfl) (by quickRfl)).1

theorem c16959 : agreeAll e16959 = true ∧ ∀ e ∈ n16959, (∀ g ∈ e.1, g.validB = true) ∧
    (∀ g ∈ e.2, g.validB = true) ∧
    EdgeNoncomm.moveCheckAux (Native.evalWord e.1 (aV ())) (Native.evalWord e.2 (aV ())) = true :=
  tp3B_sound CertificateChecks.KernelKDenseP.M13.data_ok e16959 n16959 (by quickRfl)
      (S := rlS CFSG.KD.M13.c16959.rn CFSG.KD.M13.c16959.CH CFSG.KD.M13.c16959.PRf
        CFSG.KD.M13.c16959.S0 9)
      (fun x hx => (rlS_lt (Nat.lt_of_lt_of_le hx (by decide))).trans (by interval_cases x <;> rfl))
      (CH := CFSG.KD.M13.c16959.CH) (nch := kd_count% CFSG.KD.M13.c16959 CH)
      (IT := CFSG.KD.M13.c16959.IT)
      (replay_sound (run := CFSG.KD.M13.c16959.rn) (chk := CFSG.KD.M13.chkP (tri e16959 n16959))
        (fun S S' c h3 h4 => CFSG.KC.KDenseP.chunkOKN_loc S S' c h3 h4)
        (fun S c h => CFSG.KC.KDenseP.chunkOKN_prod S c h)
        (CH := CFSG.KD.M13.c16959.CH) (PR := CFSG.KD.M13.c16959.PRf) (GK := CFSG.KD.M13.c16959.GKf)
        (G := CFSG.KD.M13.c16959.Gf) (S0 := CFSG.KD.M13.c16959.S0) (w := 9)
        (ng := kd_count% CFSG.KD.M13.c16959 u) (by kd_allE CFSG.KD.M13.c16959 u) (by quickRfl))
      (by quickRfl) (by quickRfl)

theorem gw_ne_of_moveCheckAux {w₁ w₂ : List Native.Gen} (h₁ : ∀ g ∈ w₁, g.validB = true)
    (h₂ : ∀ g ∈ w₂, g.validB = true)
    (hm : EdgeNoncomm.moveCheckAux (Native.evalWord w₁ (aV ())) (Native.evalWord w₂ (aV ())) =
      true) : gw w₁ ≠ gw w₂ := by
  obtain ⟨k, hk, hne⟩ := EdgeNoncomm.moveCheckAux_spec hm
  intro heq
  have e : wordLin w₁ (interp (aV ())) = wordLin w₂ (interp (aV ())) := by
    have := congrArg (fun g : Gmat => (g : SpaceB ≃ₗ[ℚ] SpaceB) (interp (aV ()))) heq
    simpa using this
  rw [← evalWord_sound w₁ h₁ (aV ()), ← evalWord_sound w₂ h₂ (aV ())] at e
  have hcf := EdgeNoncomm.cf_eq_of_interp_eq e hk
  apply hne
  unfold cf at hcf
  have h2 : (2 : ℚ) ^ (Native.evalWord w₁ (aV ())).e ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (2 : ℚ) ^ (Native.evalWord w₂ (aV ())).e ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_eq_div_iff h2 h3] at hcf
  exact_mod_cast hcf

theorem gw_ne_one_of_tauSep {w : List Native.Gen}
    (h : (∀ g ∈ Native.Gen.tau :: w, g.validB = true) ∧ (∀ g ∈ [Native.Gen.tau], g.validB = true) ∧
      EdgeNoncomm.moveCheckAux (Native.evalWord (Native.Gen.tau :: w) (aV ()))
        (Native.evalWord [Native.Gen.tau] (aV ())) = true) : gw w ≠ 1 := by
  intro h1
  apply gw_ne_of_moveCheckAux h.1 h.2.1 h.2.2
  have e : Native.Gen.tau :: w = [Native.Gen.tau] ++ w := rfl
  rw [e, gw_append, h1, one_mul]

theorem gw_powL_m13 (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (by simpa using wordLin_powL k w)

@[expose] def actX1 : Aff := (mul (0, 0, 11) (mul (0, 10, 0) (6, 0, 0)),
  mul (0, 0, 3) (mul (0, 7, 0) (1, 0, 0)), (0, 0, 6))

@[expose] def actX2 : Aff := (mul (0, 0, 8) (mul (0, 7, 0) (7, 0, 0)),
  mul (0, 0, 6) (mul (0, 7, 0) (5, 0, 0)), (0, 0, 1))

@[expose] def actG : Aff := ((1, 0, 0), (0, 1, 9), (0, 0, 1))

@[expose] def actC2 : Aff := ((1, 0, 4), (0, 1, 0), (0, 0, 1))

@[expose] def xact : List Bool → Aff
  | [] => ((1, 0, 0), (0, 1, 0), (0, 0, 1))
  | l :: xw => comp (xact xw) (if l then actX1 else actX2)

@[expose] def lineAct (e : CensusLine) : Aff :=
  comp (apow (if e.corrG then actG else actC2) e.j) (xact e.xw)

@[expose] def s0 : T := (8, 9, 11)

@[expose] def lineOK (e : CensusLine) : Bool :=
  bif e.toC then decide (act (lineAct e) ((e.a : ZMod 13), (e.b : ZMod 13), 0) =
    (0, (e.lam : ZMod 13), 0))
  else decide (act (lineAct e) ((e.a : ZMod 13), (e.b : ZMod 13), 0) = pw s0 e.lam)

theorem lines_ok : censusLines.all lineOK = true := by decide +kernel

theorem sq_eq_one_of_inverts {G : Type*} [Group G] {s z : G} (h : s * (z * (s * z)) = 1)
    (hs : s * z = z * s) (hss : s * s = 1) : z * z = 1 := by
  rw [hs] at h
  have h2 : z * (z * s) = s⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [inv_eq_of_mul_eq_one_right hss, ← mul_assoc] at h2
  exact mul_right_cancel (h2.trans (one_mul s).symm)

theorem pow_four_of_sq {G : Type*} [Group G] {a b : G} (h : a * a = b) (hb : b * b = 1) :
    a ^ 4 = 1 := by
  have e : a ^ 4 = a * a * (a * a) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e, h, hb]

section Group


theorem heis13 : Heis (gw genD13W0) (gw genD13W2) (gw genD13W1) := by
  obtain ⟨hx, hy, hz, hzx, hzy, hyx, -⟩ := d13_gw_facts
  exact ⟨hx, hy, hz, hzx, hzy, hyx⟩

macro "m13_nf" : tactic =>
  `(tactic| ((simp only [← heis13.ev_x, ← heis13.ev_y, ← heis13.ev_z, heis13.ev_mul,
      heis13.ev_pw, heis13.ev_mul_x, heis13.x_mul_ev, heis13.ev_mul_y, heis13.y_mul_ev,
      heis13.ev_mul_z, heis13.z_mul_ev]) <;> exact congrArg (ev _ _ _) (by decide +kernel)))

theorem acts_x1 : Acts (gw genD13W0) (gw genD13W2) (gw genD13W1) (gw genD13W3) actX1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hx1x, hx1y, -⟩ := d13_gw_facts
  refine acts_of heis13 (mul_inv_eq_of_eq_mul ?_) (mul_inv_eq_of_eq_mul ?_) (by decide +kernel)
    (by decide +kernel)
  · rw [hx1x, ← mul_assoc, ← mul_assoc]
    refine congrArg (· * gw genD13W3) ?_
    m13_nf
  · rw [hx1y, ← mul_assoc, ← mul_assoc]
    refine congrArg (· * gw genD13W3) ?_
    m13_nf

theorem acts_x2 : Acts (gw genD13W0) (gw genD13W2) (gw genD13W1) (gw genD13W4) actX2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hx2x, hx2y, -⟩ := d13_gw_facts
  refine acts_of heis13 (mul_inv_eq_of_eq_mul ?_) (mul_inv_eq_of_eq_mul ?_) (by decide +kernel)
    (by decide +kernel)
  · rw [hx2x, ← mul_assoc, ← mul_assoc]
    refine congrArg (· * gw genD13W4) ?_
    m13_nf
  · rw [hx2y, ← mul_assoc, ← mul_assoc]
    refine congrArg (· * gw genD13W4) ?_
    m13_nf

theorem acts_g : Acts (gw genD13W0) (gw genD13W2) (gw genD13W1) (gw genD13W0) actG := by
  have := acts_ev heis13 (w := (1, 0, 0)) (A := actG) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rwa [heis13.ev_one_x] at this

theorem acts_c2 : Acts (gw genD13W0) (gw genD13W2) (gw genD13W1) (gw genD13W2) actC2 := by
  have := acts_ev heis13 (w := (0, 1, 0)) (A := actC2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rwa [heis13.ev_one_y] at this

theorem acts_v : Acts (gw genD13W0) (gw genD13W2) (gw genD13W1) (gw vW13) (apow actX2 3) := by
  obtain ⟨-, -, -, -, -, -, -, hv, -⟩ := d13_gw_facts
  have hv' : gw vW13 = gw genD13W4 ^ 3 := hv
  rw [hv']
  exact acts_x2.pow heis13 3

theorem acts_xword (xw : List Bool) : Acts (gw genD13W0) (gw genD13W2) (gw genD13W1)
    (gw (xw.map fun l => if l then genD13W3 else genD13W4).flatten) (xact xw) := by
  induction xw with
  | nil =>
    rw [List.map_nil, List.flatten_nil, gw_nil]
    exact Acts.one heis13
  | cons l xw ih =>
    rw [List.map_cons, List.flatten_cons, gw_append]
    cases l
    · exact ih.mul heis13 acts_x2
    · exact ih.mul heis13 acts_x1

theorem acts_corr (e : CensusLine) : Acts (gw genD13W0) (gw genD13W2) (gw genD13W1)
    (gw (powL e.j (if e.corrG then genD13W0 else genD13W2)))
    (apow (if e.corrG then actG else actC2) e.j) := by
  rw [gw_powL_m13]
  rcases e with ⟨a, b, xw, corrG, j, toC, lam⟩
  cases corrG
  · exact acts_c2.pow heis13 j
  · exact acts_g.pow heis13 j

theorem conj_line {T C s t u : Gmat} (lam : ℕ) (hc : C * s * C⁻¹ = u)
    (ht : T * u * T⁻¹ = t ^ lam) : T * C * s = t ^ lam * (T * C) := by
  rw [mul_assoc, mul_inv_eq_iff_eq_mul.1 hc, ← mul_assoc, mul_inv_eq_iff_eq_mul.1 ht, mul_assoc]

theorem ev_ne_one {u : T} (h : mul (0, 1, 0) u = mul (mul u (0, 0, 4)) (0, 1, 0)) :
    ev (gw genD13W0) (gw genD13W2) (gw genD13W1) u ≠ 1 := by
  obtain ⟨-, -, hz13, -, -, -, hz1, -⟩ := d13_gw_facts
  intro h1
  have e : ev (gw genD13W0) (gw genD13W2) (gw genD13W1) (0, 1, 0) *
      ev (gw genD13W0) (gw genD13W2) (gw genD13W1) u =
      ev (gw genD13W0) (gw genD13W2) (gw genD13W1) u *
        ev (gw genD13W0) (gw genD13W2) (gw genD13W1) (0, 0, ((4 : ℕ) : ZMod 13)) *
        ev (gw genD13W0) (gw genD13W2) (gw genD13W1) (0, 1, 0) := by
    rw [heis13.ev_mul, heis13.ev_mul, heis13.ev_mul, h]
    rfl
  rw [h1, one_mul, mul_one, heis13.ev_z] at e
  have hz4 : gw genD13W1 ^ 4 = 1 := mul_right_cancel (e.symm.trans (one_mul _).symm)
  exact hz1 (by rw [eq_pow_four_pow hz13, hz4, one_pow])

theorem gw_bW13_ev : gw bW13 = ev (gw genD13W0) (gw genD13W2) (gw genD13W1) (1, 9, 2) := by
  rw [bW13, gw_append, gw_append, gw_powL_m13, gw_powL_m13]
  m13_nf

theorem gw_bpW13_ev : gw bpW13 = ev (gw genD13W0) (gw genD13W2) (gw genD13W1) (1, 5, 4) := by
  rw [bpW13, gw_append, gw_append, gw_powL_m13, gw_powL_m13]
  m13_nf

theorem gw_b3W13_ev : gw b3W13 = ev (gw genD13W0) (gw genD13W2) (gw genD13W1) (3, 1, 10) := by
  rw [b3W13, gw_append, gw_append, gw_powL_m13, gw_powL_m13]
  m13_nf

theorem gw_bp3W13_ev : gw bp3W13 = ev (gw genD13W0) (gw genD13W2) (gw genD13W1) (3, 2, 7) := by
  rw [bp3W13, gw_append, gw_append, gw_powL_m13, gw_powL_m13, gw_powL_m13]
  m13_nf

theorem gw_b_eq : gw bW13 = gw b3W13 ^ 9 := by
  rw [gw_bW13_ev, gw_b3W13_ev]
  m13_nf

theorem gw_bp_eq : gw bpW13 = gw bp3W13 ^ 9 := by
  rw [gw_bpW13_ev, gw_bp3W13_ev]
  m13_nf

theorem facts16958 :
    gw vW13 * gw genD13W1 = gw genD13W1 * gw vW13 ∧
      gw vW13 * gw genD13W0 ^ 6 * gw vW13 * gw genD13W0 ^ 7 = gw genD13W0 ∧
      gw vW13 * gw genD13W2 ^ 6 * gw vW13 * gw genD13W2 ^ 7 = gw genD13W2 * gw genD13W1 ^ 4 ∧
      gw tW13 * gw tW13 = 1 ∧ gw vW13 * gw tW13 = gw tW13 * gw vW13 ∧
      gw tW13 * gw genD13W1 * gw tW13 * gw genD13W1 = 1 ∧
      gw bW13 * gw tW13 = gw tW13 * gw bW13 ∧
      gw bpW13 * gw vtW13 = gw vtW13 * gw bpW13 ∧
      gw wvW13 ^ 4 = 1 ∧ gw vW13 * gw wvW13 = gw wvW13 * gw vW13 ∧
      gw genD13W1 * gw wvW13 = gw wvW13 * gw genD13W1 ∧
      gw wtW13 ^ 4 = 1 ∧ gw tW13 * gw wtW13 = gw wtW13 * gw tW13 ∧
      gw bW13 * gw wtW13 = gw wtW13 * gw bW13 ∧
      gw wtW13 * gw genD13W1 = gw genD13W1 ^ 8 * gw wtW13 ∧
      gw wvtW13 ^ 4 = 1 ∧ gw vtW13 * gw wvtW13 = gw wvtW13 * gw vtW13 ∧
      gw bpW13 * gw wvtW13 = gw wvtW13 * gw bpW13 ∧
      gw wvtW13 * gw genD13W1 = gw genD13W1 ^ 8 * gw wvtW13 ∧
      gw htW13 * gw tW13 = gw vW13 * gw htW13 ∧ gw hvtW13 * gw vtW13 = gw vW13 * gw hvtW13 ∧
      gw tW13 ≠ 1 ∧ gw vtW13 ≠ 1 ∧ gw bW13 ≠ 1 ∧ gw bpW13 ≠ 1 ∧
      gw wvW13 * gw wvW13 ≠ 1 ∧ gw wtW13 * gw wtW13 ≠ 1 ∧ gw wvtW13 * gw wvtW13 ≠ 1 := by
  obtain ⟨hx13, -, hz13, -, -, hyx, hz1, -⟩ := d13_gw_facts
  have hp := agreeAll_sound c16958
  simp only [e16958, List.forall_mem_cons, List.forall_mem_nil, gw_append, gw_nil, gw_powL_m13,
    and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, -⟩ := hp
  have hvi : (gw vW13)⁻¹ = gw vW13 := inv_eq_of_mul_eq_one_right p5
  have hvz : gw vW13 * gw genD13W1 = gw genD13W1 * gw vW13 := by
    have h := acts_v.az
    have e : (apow actX2 3).2.2 = (0, 0, ((1 : ℕ) : ZMod 13)) := by decide +kernel
    rw [e, heis13.ev_z, pow_one] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hvx : gw vW13 * gw genD13W0 ^ 6 * gw vW13 = ev (gw genD13W0) (gw genD13W2) (gw genD13W1)
      (act (apow actX2 3) (((6 : ℕ) : ZMod 13), 0, 0)) := by
    have h := acts_v.conj_ev heis13 (((6 : ℕ) : ZMod 13), 0, 0)
    rwa [hvi, heis13.ev_x] at h
  have hvy : gw vW13 * gw genD13W2 ^ 6 * gw vW13 = ev (gw genD13W0) (gw genD13W2) (gw genD13W1)
      (act (apow actX2 3) (0, ((6 : ℕ) : ZMod 13), 0)) := by
    have h := acts_v.conj_ev heis13 (0, ((6 : ℕ) : ZMod 13), 0)
    rwa [hvi, heis13.ev_y] at h
  have q1 : gw vW13 * gw genD13W0 ^ 6 * gw vW13 * gw genD13W0 ^ 7 = gw genD13W0 ^ 1 := by
    rw [hvx]
    m13_nf
  have q2 : gw vW13 * gw genD13W2 ^ 6 * gw vW13 * gw genD13W2 ^ 7 =
      gw genD13W2 ^ 1 * gw genD13W1 ^ 4 := by
    rw [hvy]
    m13_nf
  rw [pow_one] at q1 q2
  have hb : ∀ g : Gmat, gw b3W13 * g = g * gw b3W13 → gw bW13 * g = g * gw bW13 := fun g h => by
    rw [gw_b_eq]
    exact ((Commute.pow_left h 9)).eq
  have hbp : ∀ g : Gmat, gw bp3W13 * g = g * gw bp3W13 → gw bpW13 * g = g * gw bpW13 :=
    fun g h => by
      rw [gw_bp_eq]
      exact ((Commute.pow_left h 9)).eq
  have hz2 : gw genD13W1 * gw genD13W1 ≠ 1 := fun h => hz1 (by
    have e2 : 2 * 7 = 13 + 1 := rfl
    have e : (gw genD13W1 * gw genD13W1) ^ 7 = gw genD13W1 := by
      rw [← pow_two, ← pow_mul, e2, pow_add, hz13, one_mul, pow_one]
    rw [← e, h, one_pow])
  have ht1 : gw tW13 ≠ 1 := fun h => hz2 (by
    rw [h, one_mul, one_mul] at p2
    exact p2)
  have hvtd : gw vtW13 = gw tW13 * gw vW13 := gw_append _ _
  have hvt1 : gw vtW13 ≠ 1 := fun h => hz2 (by
    rw [hvtd] at h
    have htv : gw tW13 = gw vW13 := by rw [← hvi]; exact eq_inv_of_mul_eq_one_left h
    rw [htv] at p2
    exact sq_eq_one_of_inverts p2 hvz p5)
  have hv1 : gw vW13 ≠ 1 := fun h => hz1 (by
    have e : gw genD13W0 ^ 6 * gw genD13W0 ^ 7 = 1 := by rw [← pow_add]; exact hx13
    have hx1 : gw genD13W0 = 1 := q1.symm.trans (by rw [h, one_mul, mul_one, e])
    rw [hx1, mul_one, one_mul] at hyx
    have hz4 : gw genD13W1 ^ 4 = 1 := mul_left_cancel (hyx.symm.trans (mul_one _).symm)
    rw [eq_pow_four_pow hz13, hz4, one_pow])
  have hvt2 : gw vtW13 * gw vtW13 = 1 := by
    rw [hvtd, mul_assoc, ← mul_assoc (gw vW13), p1, mul_assoc, ← mul_assoc (gw tW13), p0, one_mul,
      p5]
  refine ⟨hvz, q1, q2, p0, p1, by simpa only [mul_assoc] using p2, hb _ p3, hbp _ p4,
    pow_four_of_sq p6 p5, by rw [← p6, mul_assoc], p7, pow_four_of_sq p8 p0,
    by rw [← p8, mul_assoc], hb _ p9, p10, pow_four_of_sq p11 hvt2, by rw [← p11, mul_assoc],
    hbp _ p12, p13, p14, p15, ht1, hvt1, ?_, ?_, by rw [p6]; exact hv1, by rw [p8]; exact ht1,
    by rw [p11]; exact hvt1⟩
  · rw [gw_bW13_ev]
    exact ev_ne_one (by decide +kernel)
  · rw [gw_bpW13_ev]
    exact ev_ne_one (by decide +kernel)


theorem g_s0 (h8 : gw censusGW * gw s0sqW13 = gw thirteenX * (gw thirteenX * gw censusGW)) :
    gw censusGW * ev (gw genD13W0) (gw genD13W2) (gw genD13W1) s0 * (gw censusGW)⁻¹ =
      gw thirteenX := by
  obtain ⟨hxE, -⟩ := thirteen_gw_facts
  have h2 : gw censusGW * gw s0sqW13 * (gw censusGW)⁻¹ = gw thirteenX ^ 2 :=
    mul_inv_eq_of_eq_mul (by rw [h8, pow_two, mul_assoc])
  have hs2 : gw s0sqW13 = ev (gw genD13W0) (gw genD13W2) (gw genD13W1) (pw s0 2) := by
    rw [s0sqW13, gw_append, gw_append, gw_powL_m13, gw_powL_m13, gw_powL_m13]
    m13_nf
  have hs0 : ev (gw genD13W0) (gw genD13W2) (gw genD13W1) s0 = gw s0sqW13 ^ 7 := by
    rw [hs2]
    m13_nf
  have e : 2 * 7 = 13 + 1 := rfl
  rw [hs0, ← conj_pow, h2, ← pow_mul, e, pow_add, hxE, one_mul, pow_one]

theorem census_lines
    (h8 : gw censusGW * gw s0sqW13 = gw thirteenX * (gw thirteenX * gw censusGW)) :
    ∀ e ∈ censusLines, gw (lineConjW e) * gw (lineRepW e) =
      gw (lineTargetW e) ^ e.lam * gw (lineConjW e) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hy2y, -⟩ := d13_gw_facts
  have hs0 := g_s0 h8
  have hy2 : gw genD13W6 * gw genD13W2 * (gw genD13W6)⁻¹ = gw genD13W1 :=
    mul_inv_eq_of_eq_mul (by rw [hy2y, pow_one])
  intro e he
  have hok := List.all_eq_true.1 lines_ok e he
  have hCX : Acts (gw genD13W0) (gw genD13W2) (gw genD13W1)
      (gw (powL e.j (if e.corrG then genD13W0 else genD13W2)) *
        gw (e.xw.map fun l => if l then genD13W3 else genD13W4).flatten) (lineAct e) :=
    (acts_corr e).mul heis13 (acts_xword e.xw)
  have hc := hCX.conj_ev heis13 ((e.a : ZMod 13), (e.b : ZMod 13), 0)
  have hs : gw (lineRepW e) =
      ev (gw genD13W0) (gw genD13W2) (gw genD13W1) ((e.a : ZMod 13), (e.b : ZMod 13), 0) := by
    rw [lineRepW, gw_append, gw_powL_m13, gw_powL_m13, heis13.ev_xy]
  rw [lineConjW, gw_append, gw_append, hs, lineTargetW]
  unfold lineOK at hok
  cases hC : e.toC
  · simp only [hC, cond_false, decide_eq_true_eq] at hok
    simp only [hC, Bool.false_eq_true, ↓reduceIte]
    refine conj_line e.lam (hc.trans (congrArg _ hok)) ?_
    rw [← heis13.ev_pw, ← conj_pow, hs0]
  · simp only [hC, cond_true, decide_eq_true_eq] at hok
    simp only [hC, ↓reduceIte]
    refine conj_line e.lam (hc.trans (congrArg _ hok)) ?_
    rw [heis13.ev_y, ← conj_pow, hy2]

theorem facts16959 :
    gw j1W * gw j1W = 1 ∧ gw j2W * gw j2W = 1 ∧ gw j2W * gw j1W = gw j1W * gw j2W ∧
      gw j1W * gw thirteenX = gw thirteenX * gw j1W ∧
      gw j2W * gw thirteenX = gw thirteenX * gw j2W ∧
      gw tj1W * gw j1W = gw tStarW * gw tj1W ∧ gw tj2W * gw j2W = gw tStarW * gw tj2W ∧
      gw tj12W * (gw j2W * gw j1W) = gw tStarW * gw tj12W ∧
      gw j1W ≠ 1 ∧ gw j2W ≠ 1 ∧ gw j2W * gw j1W ≠ 1 ∧
      ∀ e ∈ censusLines, gw (lineConjW e) * gw (lineRepW e) =
        gw (lineTargetW e) ^ e.lam * gw (lineConjW e) := by
  obtain ⟨he, hn⟩ := c16959
  have hp := agreeAll_sound he
  have e : e16959 = [(j1W ++ j1W, []), (j2W ++ j2W, []), (j1W ++ j2W, j2W ++ j1W),
      (thirteenX ++ j1W, j1W ++ thirteenX), (thirteenX ++ j2W, j2W ++ thirteenX),
      (j1W ++ tj1W, tj1W ++ tStarW), (j2W ++ tj2W, tj2W ++ tStarW),
      (j1W ++ j2W ++ tj12W, tj12W ++ tStarW),
      (s0sqW13 ++ censusGW, censusGW ++ thirteenX ++ thirteenX)] := rfl
  rw [e] at hp
  simp only [List.forall_mem_cons, List.forall_mem_nil, gw_append, gw_nil, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, -⟩ := hp
  have n1 := gw_ne_one_of_tauSep (hn _ List.mem_cons_self)
  have n2 := gw_ne_one_of_tauSep (hn _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have n3 := gw_ne_one_of_tauSep
    (hn _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  rw [gw_append] at n3
  exact ⟨p0, p1, p2, p3, p4, p5, p6, by simpa only [mul_assoc] using p7, n1, n2, n3,
    census_lines p8⟩

end Group

end CertificateChecks.KernelKDenseP.M13

end
