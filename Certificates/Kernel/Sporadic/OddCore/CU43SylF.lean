module

public import Certificates.Kernel.Sporadic.OddCore.CU43Syl
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43RankInputs
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.CU43Syl

open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin

theorem base : szOK 820 10 = true ∧ cK (pidn 820 10) = true ∧
    CFSG.KS.Prim.idK 820 10 (mask 10) = true ∧
    allN 5 (fun j => bAnd(cK (CU43S.GI j), Nat.beq (CU43S.G j) (pidn 820 10))) = true ∧
    Nat.beq CU43S.cnt 128 = true ∧ penumHdK (pidn 820 10) CU43S.cnt 256 CU43S.T CU43S.PL = true := by
  simpa only [bAnd_iff] using base_ok

theorem hidc : canonK 820 10 (mask 10) (820 * 10) (pidn 820 10) = true := base.2.1

theorem hid : idT 820 = tabT (unpack 820 10 (pidn 820 10)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem hcnt : CU43S.cnt = 128 := Nat.eq_of_beq_eq_true base.2.2.2.2.1

theorem gen {j : Nat} (hj : j < 5) : cK (CU43S.GI j) = true ∧ CU43S.G j = pidn 820 10 := by
  have h := (bAnd_iff _ _).1 (allN_spec base.2.2.2.1 j hj)
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem gens_eq {j : Nat} (hj : j < 5) :
    #[sylGen0, sylGen1, sylGen2, sylGen3, sylGen4][j]! = unpack 820 10 (CU43S.GI j) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
  · exact eq_unpack_of_bindListK bind0
  · exact eq_unpack_of_bindListK bind1
  · exact eq_unpack_of_bindListK bind2
  · exact eq_unpack_of_bindListK bind3
  · exact eq_unpack_of_bindListK bind4

theorem s_tabs : TabsOK 820 10 5 CU43S.GI sylTabs := by
  refine ⟨by simp [sylTabs], fun j hj => ⟨?_, (gen hj).1⟩⟩
  unfold sylTabs
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map,
    ← getElem!_pos #[sylGen0, sylGen1, sylGen2, sylGen3, sylGen4] j (by simpa using hj),
    gens_eq hj]
  rfl

theorem s_pe : ∀ i < CU43S.cnt, penumPtK 820 10 (mask 10) (820 * 10) true CU43S.G CU43S.GI 5
    CU43S.cnt CU43S.T CU43S.PL CU43S.POS CU43S.SRT CU43S.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < CU43S.cnt,
    hsortPtK 820 10 (mask 10) CU43S.cnt CU43S.T CU43S.HS CU43S.HSI i = true :=
  fun i hi => slK_spec sH i (Nat.zero_le _) (by omega) hi

theorem closure_eq : sylEnum = hRec 820 10 CU43S.cnt CU43S.T CU43S.PL :=
  (mulH_sound base.1 (fun j hj => (gen hj).2) s_tabs base.2.2.2.2.2 s_pe s_hs).1

theorem hT {i : Nat} (hi : i < 128) : canonK 820 10 (mask 10) (820 * 10) (CU43S.T i) = true :=
  penumPt_canon (s_pe i (by rw [hcnt]; exact hi))

theorem entry {i : Nat} (hi : i < 128) : sylEnum.1[i]! = tabT (unpack 820 10 (CU43S.T i)) := by
  rw [closure_eq]
  exact hRec_get (by rw [hcnt]; exact hi)

theorem comm_eq {i j : Nat} (hi : i < 128) (hj : j < 128) :
    commTT 820 sylEnum.1[i]! sylEnum.1[j]! = commK i j := by
  rw [entry hi, entry hj, commTT_unpack (hT hi) (hT hj)]
  rfl

theorem invol_eq {i : Nat} (hi : i < 128) : involOK 820 sylEnum.1[i]! = involK i := by
  rw [entry hi, involOK_unpack' (by norm_num) hid hidc (hT hi)]
  rfl

theorem card_range_filter (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    ((Finset.range n).filter p).card = (List.range n).countP fun i => decide (p i) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((List.nodup_range).filter _),
    List.toFinset_filter, List.toFinset_range]
  simp

theorem facts26015 : rankCheck = true := by
  have h := rank_ok
  unfold rankK at h
  simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  have hcent : ∀ i < 128, (∀ j < 128, commTT 820 sylEnum.1[i]! sylEnum.1[j]! = true) ↔
      centK i = true := by
    intro i hi
    simp only [centK, List.all_eq_true, List.mem_range]
    exact forall_congr' fun j => imp_congr_right fun hj => by rw [comm_eq hi hj]
  unfold rankCheck
  rw [decide_eq_true_iff]
  refine ⟨?_, fun i hi hinv hex => ?_⟩
  · rw [card_range_filter]
    refine le_trans (le_of_eq ?_) h1
    apply List.countP_congr
    intro i hi
    rw [decide_eq_true_iff, hcent i (List.mem_range.1 hi)]
  · have hc : centK i = false := by
      rcases hex with ⟨j, hj, hf⟩
      cases e : centK i
      · rfl
      · have := ((hcent i hi).2 e) j hj
        rw [this] at hf
        exact absurd hf (by decide)
    have hi2 := h2 i hi
    rw [← invol_eq hi, hinv, hc] at hi2
    simp only [Bool.not_true, Bool.false_or, Nat.ble_eq] at hi2
    rw [card_range_filter]
    refine le_trans (le_of_eq ?_) hi2
    unfold cntK
    apply List.countP_congr
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [decide_eq_true_iff, invol_eq hj', comm_eq hi hj', Bool.and_eq_true]

end CertificateChecks.KernelSpor.CU43Syl

end
