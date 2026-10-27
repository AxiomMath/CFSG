module

public import Certificates.Kernel.Sporadic.ONPv.Facts
public import Certificates.Kernel.Sporadic.ON2.Assemble
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.AlphaCheck
public import CFSG.Sporadic.Schreier.ONOuterDefs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPv

open CFSG.KS.ONPv CFSG.KS.ONNQ CFSG.KS.Words CFSG.ONSchreier CFSG.LocalAnalysis.RankThreeTheoremC.ONPair
open CFSG.Sporadic.ON CFSG.Sporadic.Th CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.ON
open CFSG.Sporadic.Bridge.ONGPL.Native
open TauCeti (SporadicName)

theorem items_rels : (List.range 29).map (fun j => wd (OPV.D (178 + j))) =
    (rels ()).map fun r => r.map letterOf := by
  decide +kernel

theorem items_surj : wd (OPV.D 207) = decW (SRW.WC 0) (SRW.WL 0) ∧
    wd (OPV.D 208) = decW (SRW.WC 1) (SRW.WL 1) := by
  decide +kernel

theorem surjWords_items : (surjWords ())[0]! = wd (OPV.D 207) ∧
    (surjWords ())[1]! = wd (OPV.D 208) := by
  rw [KernelSpor.ON2.surj_words, items_surj.1, items_surj.2]
  exact ⟨rfl, rfl⟩

theorem wordProd_eq_wv {n : Nat} (g : Nat → Equiv.Perm (Fin n)) (r : List (Nat × Bool)) :
    wordProd g r = wv g (r.map letterOf) := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    rw [List.map_cons, wv_cons, ← ih]
    simp only [wordProd, List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · have h1 : ¬ (0 : Int) < -((i : Int) + 1) := by omega
      have h2 : (-(-((i : Int) + 1))).toNat - 1 = i := by omega
      simp [lv, letterOf, h1, h2]
    · have h1 : (0 : Int) < (i : Int) + 1 := by omega
      have h2 : ((i : Int) + 1).toNat - 1 = i := by omega
      simp [lv, letterOf, h1, h2]

section Alpha


noncomputable def vP (k : Nat) : Pv :=
  if h : k < 7 then ⟨gI sgen OPV.D k, gI_mem sgen_mem7 items_ok (Or.inl (by omega))⟩ else 1

theorem coe_vP : ∀ k < 7, ((vP k : Pv) : Equiv.Perm (Fin 245520)) = gI sgen OPV.D k := by
  intro k hk
  rw [vP, dif_pos hk]

theorem wv_vP {w : List Int} (hw : Lm 7 w) :
    wv (fun k => ((vP k : Pv) : Equiv.Perm (Fin 245520))) w = wv (gI sgen OPV.D) w :=
  wv_congr coe_vP hw

theorem relators_vP : ∀ r ∈ TauCeti.Sporadic.onanPresentation.relatorLetters, wordProd vP r = 1 := by
  rw [relatorLetters_eq]
  intro r hr
  have hm : r.map letterOf ∈ (List.range 29).map (fun j => wd (OPV.D (178 + j))) := by
    rw [items_rels]
    exact List.mem_map_of_mem hr
  obtain ⟨j, hj, e⟩ := List.mem_map.1 hm
  have hj' : j < 29 := List.mem_range.1 hj
  apply Subtype.ext
  have hc : ((wordProd vP r : Pv) : Equiv.Perm (Fin 245520)) =
      wordProd (fun k => ((vP k : Pv) : Equiv.Perm (Fin 245520))) r := by
    change Pv.subtype (wordProd vP r) = _
    simp only [wordProd, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    simp only [Function.comp_apply]
    split <;> simp
  rw [hc, wordProd_eq_wv, ← e, wv_vP (items_hi items_ok (178 + j)), pv502.1 j hj']
  rfl

noncomputable def toPv : TauCeti.Sporadic.onanPresentation.Group →* Pv :=
  presHom TauCeti.Sporadic.onanPresentation vP relators_vP

theorem coe_toPv_wordG : ∀ {w : List Int}, Lm 7 w →
    ((toPv (wordG presLetter w) : Pv) : Equiv.Perm (Fin 245520)) = wv (gI sgen OPV.D) w
  | [], _ => by simp [wordG, wv_nil]
  | z :: w, hw => by
    obtain ⟨⟨h0, h7⟩, hw'⟩ := Lm_cons hw
    have e : wordG presLetter (z :: w) = presLetter z * wordG presLetter w := by
      simp only [wordG, List.map_cons, List.prod_cons]
    rw [e, map_mul, Subgroup.coe_mul, coe_toPv_wordG hw', wv_cons]
    congr 1
    unfold presLetter lv toPv
    by_cases hp : 0 < z
    · rw [if_pos hp, if_pos hp, presHom_presGen _ _ _ (by rw [generatorCount_eq]; omega),
        coe_vP _ (by omega), show (z - 1).toNat = z.toNat - 1 by omega]
    · rw [if_neg hp, if_neg hp, map_inv, presHom_presGen _ _ _ (by rw [generatorCount_eq]; omega),
        InvMemClass.coe_inv, coe_vP _ (by omega), show (-z - 1).toNat = (-z).toNat - 1 by omega]

theorem gI79_eq : gI sgen OPV.D 79 = evalS alphaWordA := by
  have h := items_hi items_ok 79
  rw [items_main.2.2.1] at h
  rw [gI, items_main.2.2.1, evalS, evalWord_eq_wv sgen h]

theorem toPv_surjA : toPv (wordG presLetter (surjWords ())[0]!) = ⟨evalS alphaWordA, evalS_mem _⟩ := by
  apply Subtype.ext
  rw [surjWords_items.1, coe_toPv_wordG (items_hi items_ok 207), pv502.2.1, gI79_eq]

theorem toPv_surjB : toPv (wordG presLetter (surjWords ())[1]!) = ⟨a1, a1_mem⟩ := by
  apply Subtype.ext
  rw [surjWords_items.2, coe_toPv_wordG (items_hi items_ok 208), pv502.2.2]
  exact cert_on_schreier_action_data.2.2.2.2.2.2.1


theorem wordG_surj_ga : wordG imgG (surjWords ())[0]! = ga :=
  eq_of_tupleEq (rep_surjWord (by decide)) rep_ga bridge_facts.surjA

theorem wordG_surj_gb : wordG imgG (surjWords ())[1]! = gb :=
  eq_of_tupleEq (rep_surjWord (by decide)) rep_gb bridge_facts.surjB

theorem toJ_wordG {w : List Int} (hw : ∀ z ∈ w, z.natAbs ≤ 7) :
    toJ (wordG presLetter w) = wordG imgG w := by
  unfold wordG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  exact toJ_presLetter (hw z hz)

private theorem presentation_ONan_eq :
    SporadicName.ONan.presentation = TauCeti.Sporadic.onanPresentation := rfl

theorem toJ_bijective : Function.Bijective toJ := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Presentation.ONan.finite_card_le
  revert hfin hcard
  show Finite SporadicName.ONan.presentation.Group →
    Nat.card SporadicName.ONan.presentation.Group ≤ 460815505920 → _
  rw [presentation_ONan_eq]
  intro hfin hcard
  have hcard' : Nat.card TauCeti.Sporadic.onanPresentation.Group ≤ Nat.card J := by
    rw [card_J]
    exact hcard
  exact toJ_surjective.bijective_of_nat_card_le hcard'

noncomputable def toJequiv : TauCeti.Sporadic.onanPresentation.Group ≃* J :=
  MulEquiv.ofBijective toJ toJ_bijective

theorem surjLetters {i : Nat} (hi : i < 2) : ∀ z ∈ (surjWords ())[i]!, z.natAbs ≤ 7 :=
  fun z hz => (bridge_facts.letters _ (surjWords_mem hi) z hz).2

theorem toJequiv_symm_ga : toJequiv.symm ga = wordG presLetter (surjWords ())[0]! := by
  rw [MulEquiv.symm_apply_eq]
  change ga = toJ _
  rw [toJ_wordG (surjLetters (by decide)), wordG_surj_ga]

theorem toJequiv_symm_gb : toJequiv.symm gb = wordG presLetter (surjWords ())[1]! := by
  rw [MulEquiv.symm_apply_eq]
  change gb = toJ _
  rw [toJ_wordG (surjLetters (by decide)), wordG_surj_gb]

noncomputable def betaJ : J →* Pv := toPv.comp (toJequiv.symm : J →* _)

theorem betaJ_ga : betaJ ga = ⟨evalS alphaWordA, evalS_mem _⟩ := by
  rw [betaJ, MonoidHom.comp_apply]
  change toPv (toJequiv.symm ga) = _
  rw [toJequiv_symm_ga, toPv_surjA]

theorem betaJ_gb : betaJ gb = ⟨a1, a1_mem⟩ := by
  rw [betaJ, MonoidHom.comp_apply]
  change toPv (toJequiv.symm gb) = _
  rw [toJequiv_symm_gb, toPv_surjB]

theorem betaJ_injective : Function.Injective betaJ := by
  have := isSimpleGroup_J
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases (betaJ.normal_ker).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have : ga ∈ betaJ.ker := h ▸ Subgroup.mem_top ga
    rw [MonoidHom.mem_ker, betaJ_ga] at this
    apply pv502_hd
    rw [gI79_eq]
    exact congrArg Subtype.val this

noncomputable def gammaPv : Pv →* Pv := betaJ.comp (jEquivPv.symm : Pv →* J)

theorem gammaPv_injective : Function.Injective gammaPv :=
  betaJ_injective.comp jEquivPv.symm.injective

noncomputable def alphaPv : Pv ≃* Pv :=
  MulEquiv.ofBijective gammaPv (Finite.injective_iff_bijective.1 gammaPv_injective)

theorem jEquivPv_symm_a0 : jEquivPv.symm ⟨a0, a0_mem⟩ = ga := by
  rw [MulEquiv.symm_apply_eq]
  exact (Subtype.ext phiV_ga).symm

theorem jEquivPv_symm_a1 : jEquivPv.symm ⟨a1, a1_mem⟩ = gb := by
  rw [MulEquiv.symm_apply_eq]
  exact (Subtype.ext phiV_gb).symm

theorem alphaPv_facts : alphaPv ⟨a0, a0_mem⟩ = ⟨evalS alphaWordA, evalS_mem _⟩ ∧
    alphaPv ⟨a1, a1_mem⟩ = ⟨a1, a1_mem⟩ := by
  refine ⟨?_, ?_⟩
  · change betaJ (jEquivPv.symm ⟨a0, a0_mem⟩) = _
    rw [jEquivPv_symm_a0, betaJ_ga]
  · change betaJ (jEquivPv.symm ⟨a1, a1_mem⟩) = _
    rw [jEquivPv_symm_a1, betaJ_gb]

end Alpha

end CertificateChecks.KernelSpor.ONPv

end
