
module

public import Certificates.Kernel.Fi23M.Psi
public import Certificates.Kernel.Fi23M.Keys
public import Certificates.Kernel.Fi23C.Group
public import Certificates.Kernel.Fi23R.Sound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.Sporadic.Fi23.Transposition
import all Certificates.Kernel.Fi23M.Psi
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Mathlib
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23SylowBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Co2Schreier.ThirdChain
public import CFSG.Sporadic.Fi22
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.Walter.JRFacts
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate131101Base
public import Certificates.Certificate13620Base
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Q

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native
  CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.Perm CertificateChecks.KernelFi23M
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev ρ : CFSG.Sporadic.Fi23.J →* Equiv.Perm (Fin 31671) :=
  MulAction.toPermHom CFSG.Sporadic.Fi23.J (Fin 31671)

theorem ρ_acts (g : CFSG.Sporadic.Fi23.J) : ActsAs (ρ g) (idx 31671 g) :=
  fun x hx => by
    rw [idx_of_lt g hx]
    rfl

theorem orb_eq : orb = orbLit :=
  orbitData_eq'

theorem a_acts :
    ActsAs (ρ a) (tb G 39) := by
  intro x hx
  rw [ρ_acts a x hx, ← CFSG.Sporadic.Fi23.rep_alpha x hx, orb_eq]
  exact ap_tabOf 39 hx

theorem b_acts :
    ActsAs (ρ b) (tb G 40) := by
  intro x hx
  rw [ρ_acts b x hx, ← CFSG.Sporadic.Fi23.rep_beta x hx, orb_eq]
  exact ap_tabOf 40 hx

theorem rels_img :
    ∀ w ∈ P23.relatorLetters, wordVal CFSG.Sporadic.Bridge.Fi23.img w = 1 := by
  intro w hw
  rw [relatorLetters_P23] at hw
  exact CFSG.Sporadic.Bridge.Fi23.relators_eval w
    (by rw [CFSG.Sporadic.Bridge.Fi23.relatorLetters_eq]; exact hw)

noncomputable def τ : PG →* CFSG.Sporadic.Fi23.J :=
  presHom P23 CFSG.Sporadic.Bridge.Fi23.img rels_img

theorem τ_gen {k : ℕ}
    (hk : k < 10) : τ (gen k) = CFSG.Sporadic.Bridge.Fi23.img k := by
  unfold gen
  rw [dif_pos (by rw [generatorCount_P23]; exact hk)]
  exact presHom_of P23 _ rels_img _

theorem X9_img : ∀ k < 10, X9 k =
    ((CFSG.Sporadic.Bridge.Fi23GPL.Native.imgWords ())[k]!.map fun z =>
      if z = 1 then mA else if z = -1 then mA⁻¹ else if z = 2 then mB else mB⁻¹).prod :=
  (Classical.choose_spec (Certificates.certificate9206).2.2.2).1

theorem mat_τ (p : PG) :
    mat (τ p) = (σ p).val := by
  have e : (CFSG.Sporadic.Fi23.J.subtype.comp τ : PG →* GL (Fin 253) (ZMod 3)) = σ := by
    apply PresentedGroup.ext
    intro i
    have hi : i.val < 10 := lt_of_lt_of_eq i.isLt generatorCount_P23
    have e1 : (PresentedGroup.of i : PG) = gen i.val := by
      unfold gen
      rw [dif_pos i.isLt]
    rw [e1, MonoidHom.comp_apply, τ_gen hi, σ_gen hi]
    apply Units.ext
    rw [u_val hi]
    exact CFSG.Sporadic.Bridge.Fi23.mat_img X9_img hi
  exact congrArg (fun f : PG →* GL (Fin 253) (ZMod 3) => ((f p : GL (Fin 253) (ZMod 3)) :
    Matrix (Fin 253) (Fin 253) (ZMod 3))) e

theorem τ_wα : τ wα = CFSG.Sporadic.Fi23.a :=
  mat_injective (by rw [mat_τ, σ_wα, mat_a])

theorem τ_wβ : τ wβ = CFSG.Sporadic.Fi23.b :=
  mat_injective (by rw [mat_τ, σ_wβ, mat_b])

theorem τ_bijective :
    Function.Bijective τ := by
  have hsurj : Function.Surjective τ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← CFSG.Sporadic.Fi23.closure_ab, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨wα, τ_wα⟩
    · exact ⟨wβ, τ_wβ⟩
  obtain ⟨hf, hc⟩ := CFSG.Sporadic.Presentation.Fi23.finite_card_le
  have : Finite PG := hf
  have hc' : Nat.card PG ≤ Nat.card CFSG.Sporadic.Fi23.J := by
    rw [card_J]
    exact hc
  exact hsurj.bijective_of_nat_card_le hc'

theorem closure_w :
    Subgroup.closure ({wα, wβ} : Set PG) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  have h1 : τ p ∈ (Subgroup.closure ({wα, wβ} : Set PG)).map τ := by
    rw [MonoidHom.map_closure, Set.image_pair, τ_wα, τ_wβ, CFSG.Sporadic.Fi23.closure_ab]
    exact Subgroup.mem_top _
  obtain ⟨q, hq, e⟩ := Subgroup.mem_map.1 h1
  rw [← τ_bijective.1 e]
  exact hq

theorem ρ_τ
    (p : PG) : ρ (τ p) = phiX p := by
  have e : ρ.comp τ = phiX := by
    apply MonoidHom.eq_of_eqOn_dense closure_w
    intro x hx
    rcases hx with rfl | rfl
    · rw [MonoidHom.comp_apply, τ_wα]
      exact ActsAs.ext a_acts phiX_wα
    · rw [MonoidHom.comp_apply, τ_wβ]
      exact ActsAs.ext b_acts phiX_wβ
  exact DFunLike.congr_fun e p

theorem img_acts
    {k : ℕ} (hk : k < 10) :
    ∀ x < 31671, idx 31671 (CFSG.Sporadic.Bridge.Fi23.img k) x = tb G k x := by
  intro x hx
  rw [← ρ_acts _ x hx, ← τ_gen hk, ρ_τ, phiX_gen hk]
  exact xS_acts hk x hx

theorem letter_acts
    {l : ℕ} (hl : l < 24) :
    ∀ x < 31671, idx 31671 (pairG gs l) x = tb G (52 + l) x := by
  intro x hx
  have hsz : l < CFSG.Sporadic.Fi23.letters.size := by
    rw [letters_size, chainWords_size]
    omega
  rw [← rep_pairG_all l hsz x hx]
  have e : CFSG.Sporadic.Fi23.letters = chainLetters orbLit := by
    rw [← orb_eq]
  rw [e]
  exact ((letters_TR.2 l hl).2 x hx).1

theorem conjPt_acts
    {k : ℕ} (hk : k < 31671) :
    ∀ m < 31671, idx 31671 (conjPt k) m = CFSG.KC.Fi23R.tA G k m := by
  intro m hm
  have hal : Rep 31671 orbLit.alpha a := by
    rw [← orb_eq]
    exact CFSG.Sporadic.Fi23.rep_alpha
  have hbe : Rep 31671 orbLit.beta b := by
    rw [← orb_eq]
    exact CFSG.Sporadic.Fi23.rep_beta
  have hbi : Rep 31671 (genTables orbLit (-2)) b⁻¹ := by
    have h := rep_gen (-2)
    have e : genG (-2) = b⁻¹ := by
      unfold genG
      simp only [show (-2 : ℤ) ≠ 1 by decide, show (-2 : ℤ) ≠ -1 by decide,
        show (-2 : ℤ) ≠ 2 by decide, ite_false]
    rw [e, orb_eq] at h
    exact h
  have hD : Rep 31671 (dTable orbLit) d := by
    have h : Rep 31671 (dTable orb) d := Rep.powT (by norm_num) (rep_dWordTab dWord) 7
    rw [orb_eq] at h
    exact h
  have hc : ∀ k, conjPt k = if 0 < k ∧ ap orbLit.par k < k then
      (if ap orbLit.lab k = 1 then a else b) * conjPt (ap orbLit.par k) *
        (if ap orbLit.lab k = 1 then a else b)⁻¹ else d := by
    intro k
    rw [conjPt_eq, orb_eq]
  have hspec := treeAct_spec hal hbe hbi hD a_inv conjPt hc k m hm
  rw [← hspec]
  exact CertificateChecks.KernelFi23R.tAf_treeAct
    (fun _ hm => CertificateChecks.KernelFi23C.dTable_ap hm)
    (fun _ hm => CertificateChecks.KernelFi23C.bi_ap hm) 200 k hk (dep_pt hk).1 m hm

theorem wv_eq_of {F : ℕ → ℕ} {E : ℕ → CFSG.Sporadic.Fi23.J} {P : ℕ → Prop}
    (hE : ∀ r, P r → ∀ x < 31671, tb F r x = idx 31671 (E r) x) :
    ∀ w : List ℕ, (∀ r ∈ w, P r) → ∀ x < 31671, wv F w x = idx 31671 (w.map E).prod x
  | [], _, x, _ => by
    rw [List.map_nil, List.prod_nil, idx_one]
    rfl
  | r :: w, hw, x, hx => by
    rw [wv_cons, wv_eq_of hE w (fun s hs => hw s (List.mem_cons_of_mem r hs)) x hx,
      hE r (hw r List.mem_cons_self) _ (idx_lt _ hx), List.map_cons, List.prod_cons, idx_mul]

@[expose] noncomputable def regE (r : ℕ) : CFSG.Sporadic.Fi23.J :=
  if r < 10 then CFSG.Sporadic.Bridge.Fi23.img r else pairG gs (r - 52)

@[expose] def RegOK (r : ℕ) : Prop := r < 10 ∨ (52 ≤ r ∧ r < 76)

theorem regE_acts
    (r : ℕ) (hr : RegOK r) :
    ∀ x < 31671, tb G r x = idx 31671 (regE r) x := by
  intro x hx
  unfold regE
  rcases hr with hr | ⟨h1, h2⟩
  · rw [if_pos hr, img_acts hr x hx]
  · rw [if_neg (by omega), letter_acts (by omega) x hx]
    congr 1
    omega

theorem wvG_eq
    (w : List ℕ) (hw : ∀ r ∈ w, RegOK r) :
    ∀ x < 31671, wv G w x = idx 31671 (w.map regE).prod x :=
  wv_eq_of regE_acts w hw

theorem regE_letter (l : ℕ) : regE (Nat.add 52 l) = pairG gs l := by
  unfold regE
  rw [if_neg (by change ¬ 52 + l < 10; omega)]
  congr 1
  change 52 + l - 52 = l
  omega

end CertificateChecks.KernelFi23Q

end
