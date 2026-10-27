
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSFacts
import Certificates.Kernel.HSDc.Final
import Certificates.Kernel.HSQuot.Final
import Certificates.Kernel.HSA312.Struct
import Certificates.Kernel.HSA312.Y1
import Certificates.Kernel.HSA312.Y2
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSDc
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSBase
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSKInputs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsKInputs
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsPCore
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsMemBase
import CFSG.Quasithin.Background.A312SporHSKInputs
import CFSG.Quasithin.Background.A312SporHSBase
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSBase
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 100000

namespace CertificateChecks.HSF

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.Quasithin.A312S CFSG.Quasithin.A312S.HS CFSG.Quasithin.A312Hs

theorem hs_o2OK_K : O2OK ptAct hsLatK hsOtK := by
  have h := CFSG.KD.HSDc.facts
  refine ⟨by rw [HSK.mw_size h]; rfl, fun j hj => ?_⟩
  have hj' : j < 5 := by rw [HSK.mw_size h] at hj; exact hj
  have hOm : hsLatK.Om[j]!.lbl.size = #[1, 15, 21, 3, 3][j]! := by
    have e := h.2.2.2.2.2.2.2.1
    have hjO : j < hsLatK.Om.size := by
      have := congrArg Array.size e
      simp only [Array.size_map] at this
      rw [this]
      simpa using hj'
    rw [← e, getElem!_pos _ j hjO, getElem!_pos _ j (by simpa using hjO), Array.getElem_map]
  refine ⟨by rw [hOm]; interval_cases j <;> rfl, ?_⟩
  have h1 := (HSK.mems_ok' h hj').1
  rw [← HSK.msize h hj'] at h1
  have hlt := (HSK.om_spec (HSK.good_m h hj') HSK.delta_lt h1).2
  rw [HSK.Om_get hj', HSK.Ot_get hj']
  refine HSK.ot_spec (letters := hsSTabs.toArray) (M := fun l => CFSG.KD.HSDc.L (Nat.add 2 l))
    (fun l hl => HSK.good_s h (by simpa [HSK.sTabs_len] using hl)) (fun x hx p hp => ?_)
    (HSK.mems_ok' h hj').2
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact hlt i hi p (by rwa [getElem!_pos _ i hi])

theorem hs_spec : HSLatSpec :=
  ⟨HSK.hsK_membersOK CFSG.KD.HSDc.facts, (HSK.dc_facts CFSG.KD.HSDc.facts).1,
    (HSK.dc_facts CFSG.KD.HSDc.facts).2, hs_o2OK_K, CFSG.KD.HSDc.facts.2.2.2.2.2.2.2.1,
    CFSG.KD.HSDc.facts.2.2.2.2.2.2.2.2.2⟩

section Lat

variable [HSLat]

theorem o2_card (j : ℕ) (hj : j < 5) :
    Nat.card (CFSG.Open.pCoreOf 2 (hsCtx.Y j)) = 2 ^ 9 / #[1, 8, 8, 2, 2][j]! := by
  have hJ : j < hsCtx.J := by rw [hs_J]; exact hj
  rw [(hsCtx.memStmt_default hs_o2OK hJ).2.1]
  change 2 ^ 9 / hsOtK[j]!.lbl.size = _
  rw [hs_Ot_size j hj]

theorem quot1 : HSQuot1Fact := by
  intro _ N _ hp
  have hjJ : 1 < hsCtx.J := by rw [hs_J]; norm_num
  have h1 := hsCtx.quot_bound hjJ hsB (base_lt hs_facts) (base_property hs_facts) hsQuot1
    hsQuotEnumK.1 hsQuotEnumK.2.1 hsQuotEnumK.2.2 3840 CFSG.KD.HSQuot.quot1 N hp
  have h2 : Nat.card (hsCtx.Y 1) = 7680 := by
    rw [hs_member_card 1 (by norm_num)]; rfl
  change Nat.card ((hsCtx.Y 1) ⧸ N) ≤ 2
  omega

theorem incl_iff {j jj : ℕ} (hj : j < 5) (hjj : jj < 5) :
    hsCtx.Y j ≤ hsCtx.Y jj ↔ jj ∈ hsIncl[j]! := by
  have hJ := hs_J
  rw [hsCtx.Y_le_iff (by omega) (by omega)]
  exact inclPt_iff.mp CFSG.KD.HSA312.struct.1 j hj jj hjj

theorem incl : HSInclFact := fun j hj jj hjj => incl_iff hj hjj

theorem struct : HSStructFact := by
  intro _
  have hp1 : Nat.card (CFSG.pCore 2 ↥(hsCtx.Y 1)) = 2 ^ 6 :=
    card_pCore_of_card_pCoreOf ((o2_card 1 (by norm_num)).trans (by norm_num))
  have hp2 : Nat.card (CFSG.pCore 2 ↥(hsCtx.Y 2)) = 2 ^ 6 :=
    card_pCore_of_card_pCoreOf ((o2_card 2 (by norm_num)).trans (by norm_num))
  refine ⟨?_, ?_, fun N _ hp => ?_⟩
  · have hj : 1 < hsCtx.J := by rw [hs_J]; norm_num
    obtain ⟨x, hxY, h0, hinj, hmul, hconj⟩ :=
      explOK_sound hsCtx (base_lt hs_facts) (base_property hs_facts) hj CFSG.KD.HSA312.struct.2.1
    exact isZ4StarExtra2_pCore_of_data rfl hxY h0 hinj hmul hconj hp1
  · have hj : 2 < hsCtx.J := by rw [hs_J]; norm_num
    obtain ⟨x, hxY, h0, hinj, hmul, hconj⟩ :=
      explOK_sound hsCtx (base_lt hs_facts) (base_property hs_facts) hj CFSG.KD.HSA312.struct.2.2
    exact isZ4Cubed_pCore_of_data rfl hxY h0 hinj hmul hconj hp2
  · have hj : 2 < hsCtx.J := by rw [hs_J]; norm_num
    have h1 := hsCtx.quot_bound hj hsB (base_lt hs_facts) (base_property hs_facts)
      CFSG.Quasithin.A312Hs.hsQuot2 hsQuot2EnumK.1 hsQuot2EnumK.2.1 hsQuot2EnumK.2.2 10752 CFSG.KD.HSQuot.quot2 N hp
    have h2 : Nat.card (hsCtx.Y 2) = 10752 := by
      rw [hs_member_card 2 (by norm_num)]
      rfl
    omega

theorem hsE1_tabs : genTabs hsData.n hsE1 = hsL1K := by
  rw [hsE1, hsCtx.Y_letters (by rw [hs_J]; norm_num)]
  rfl

theorem hsE1_size : hsE1.toArray.size = 4 := by
  rw [List.size_toArray, ← genTabs_length (n := hsData.n), hsE1_tabs]
  exact CFSG.KD.HSA312.y1.1

theorem hsE1_hel : ∀ l < hsE1.toArray.size,
    hsL1K.toArray.getD l #[] = (tab hsData.n (hsE1.toArray.getD l 1)).toArray := by
  rw [← hsE1_tabs]
  exact genTabs_hel hsE1

theorem hsZ4Elt_tab : (tab hsData.n hsZ4Elt).toArray = hsZ4K := by
  have hw : ∀ l ∈ hsZ4Word, l < hsE1.toArray.size := by
    rw [hsE1_size]
    decide
  rw [hsZ4K, wordTabA_eq hsE1.toArray hsL1K.toArray hsE1_hel hsZ4Word hw]
  rfl

theorem hsEElts_tabs : genTabs hsData.n hsEElts = hsEK := by
  have hw : ∀ w ∈ hsEWords, ∀ l ∈ w, l < hsE1.toArray.size := by
    rw [hsE1_size]
    decide
  unfold genTabs hsEElts hsEK
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw'
  rw [Function.comp_apply, wordTabA_eq hsE1.toArray hsL1K.toArray hsE1_hel w (hw w hw')]

theorem hs_V1 : CFSG.Quasithin.IsZ4StarExtra2 ↥(Subgroup.closure {x | x ∈ hsZ4Elt :: hsEElts}) ∧
    Nat.card (Subgroup.closure {x | x ∈ hsZ4Elt :: hsEElts}) = 64 := by
  have h := CFSG.KD.HSA312.y1.2.2.2
  rw [← hsZ4Elt_tab, ← hsEElts_tabs] at h
  exact z4StarOK_spec (base_lt hs_facts) (base_property hs_facts) hsZ4Elt hsEElts h

theorem a1 : HSA1Fact := by
  intro _
  refine ⟨hs_V1.1, hs_V1.2, ?_⟩
  have hodd : hsLatK.Om[1]!.lbl.size % 2 = 1 := by
    rw [hs_Om_size 1 (by norm_num)]
    rfl
  refine pCoreOf_eq_closure_of_fixes hsCtx (by rw [hs_J]; norm_num) hodd _ (fun g hg => ?_) ?_
  · have ht : (tab hsData.n g).toArray ∈ hsZ4K :: hsEK := by
      rw [← hsZ4Elt_tab, ← hsEElts_tabs, ← genTabs_cons]
      exact tab_mem_genTabs hg
    exact fixes_of_fixLabs (List.all_eq_true.mp CFSG.KD.HSA312.y1.2.2.1 _ ht)
  · rw [hs_V1.2, o2_card 1 (by norm_num)]
    rfl

theorem hsE2_tabs : genTabs hsData.n hsE2 = hsL2K := by
  rw [hsE2, hsCtx.Y_letters (by rw [hs_J]; norm_num)]
  rfl

theorem hsL2_size : hsL2K.toArray.size = 4 := by
  rw [List.size_toArray]
  exact CFSG.KD.HSA312.y2.1

theorem hsE2_size : hsE2.toArray.size = 4 := by
  rw [List.size_toArray, ← genTabs_length (n := hsData.n), hsE2_tabs]
  exact CFSG.KD.HSA312.y2.1

theorem hsE2_hel : ∀ l < hsE2.toArray.size,
    hsL2K.toArray.getD l #[] = (tab hsData.n (hsE2.toArray.getD l 1)).toArray := by
  rw [← hsE2_tabs]
  exact genTabs_hel hsE2

theorem hs_hM : ∀ l < hsL2K.toArray.size, ∀ i : Fin 3,
    e8Col (hsVMats.getD l []) i = e8Vec fun r => hsMat l r i := by
  rw [hsL2_size]
  decide +kernel

theorem hs_hv (i : Fin 3) : (tab hsData.n (hsV i)).toArray = hsVTabsK.getD i #[] := by
  have hw : ∀ i : Fin 3, ∀ l ∈ hsVWords.getD i [], l < hsE2.toArray.size := by
    rw [hsE2_size]
    decide
  have h1 : hsVTabsK.getD i #[] = wordTabA hsL2K.toArray hsData.n (hsVWords.getD i []) := by
    fin_cases i <;> rfl
  rw [h1, wordTabA_eq hsE2.toArray hsL2K.toArray hsE2_hel _ (hw i)]
  rfl

theorem hs_e8 : E8Basis hsV ∧ ∀ l < hsL2K.toArray.size, ∀ i : Fin 3,
    hsLetter l * hsV i * (hsLetter l)⁻¹ = e8Elt hsV fun r => hsMat l r i := by
  refine e8_of_check (B := hsB) (base_lt hs_facts) (base_property hs_facts) hs_hv
    (fun l hl => ?_) hs_hM CFSG.KD.HSA312.y2.2.1
  rw [hsLetter, hsE2_hel l (by rw [hsE2_size]; exact hsL2_size ▸ hl)]

theorem hsWElts_tabs : genTabs hsData.n hsWElts = hsWK := by
  have hw : ∀ w ∈ hsWWords, ∀ l ∈ w, l < hsE2.toArray.size := by
    rw [hsE2_size]
    decide
  unfold genTabs hsWElts hsWK
  rw [List.map_map]
  apply List.map_congr_left
  intro w hw'
  rw [Function.comp_apply, wordTabA_eq hsE2.toArray hsL2K.toArray hsE2_hel w (hw w hw')]

theorem hs_W : CFSG.Quasithin.IsZ4Cubed ↥(Subgroup.closure {x | x ∈ hsWElts}) ∧
    Nat.card (Subgroup.closure {x | x ∈ hsWElts}) = 64 := by
  have h := CFSG.KD.HSA312.y2.2.2.2.2
  rw [← hsWElts_tabs] at h
  exact z4CubedOK_spec (base_lt hs_facts) (base_property hs_facts) hsWElts h

theorem a2 : HSA2Fact := by
  intro _
  refine ⟨by simpa using hsE2_size, hs_e8.1, fun l hl i => hs_e8.2 l (by rw [hsL2_size]; exact hl) i,
    hs_W.1, hs_W.2, ?_⟩
  have hodd : hsLatK.Om[2]!.lbl.size % 2 = 1 := by
    rw [hs_Om_size 2 (by norm_num)]
    rfl
  refine pCoreOf_eq_closure_of_fixes hsCtx (by rw [hs_J]; norm_num) hodd _ (fun g hg => ?_) ?_
  · have ht : (tab hsData.n g).toArray ∈ hsWK := by
      rw [← hsWElts_tabs]
      exact tab_mem_genTabs hg
    exact fixes_of_fixLabs (List.all_eq_true.mp CFSG.KD.HSA312.y2.2.2.2.1 _ ht)
  · rw [hs_W.2, o2_card 2 (by norm_num)]
    rfl

end Lat

end CertificateChecks.HSF

public section

namespace CertificateChecks.HSF

open CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.Quasithin.A312S

theorem facts :
    HSLatSpec ∧ HSQuot1Fact ∧ HSInclFact ∧ HSStructFact ∧ HSA1Fact ∧ HSA2Fact := by
  have : HSLat := ⟨hs_spec⟩
  exact ⟨hs_spec, fun {_} => quot1, fun {_} => incl, fun {_} => struct, fun {_} => a1,
    fun {_} => a2⟩

end CertificateChecks.HSF
