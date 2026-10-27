module

public import Certificates.Kernel.TwoHS.HarSK
public import Certificates.Kernel.TwoHS.FourGlue
public import Certificates.Kernel.HS3850.CoverFacts
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.Spor.MulHFSound
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Misc.RuInvHash
public import CFSG.Certificates.Kernel.Spor.ClassOneH

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.HN
open CFSG.KD.LQT.C4126 CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.TwoHS

theorem hnS : szOK 3850 12 = true := by decide

theorem sbase_parts :
    (∀ j < 4, invK (sG j) = true) ∧
    (∀ j < 4, sA j = wfoldR ls8 (sdW.getD (2 * j) []) ∧
      sB j = wfoldR ls8 (sdW.getD (2 * j + 1) []) ∧ invK (sA j) = true ∧ invK (sB j) = true) ∧
    SD.cnt = 64 ∧ penumHdK idn SD.cnt 200 SD.T SD.PL = true ∧
    (∀ j < 4, SD.GI j = DK j ∧ SD.G j = idn ∧ invSK (SD.GI j) (SDI j) = true) ∧
    (∀ c < 16, r32 SDM c < SD.cnt ∧
      SD.T (r32 SDM c) = sComm (sG (c / 4)) (sG (c % 4))) := by
  have h := harS_base
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, -, a4, a5, a6, a7⟩ := h
  refine ⟨fun j hj => allN_spec a1 j hj, fun j hj => ?_, Nat.eq_of_beq_eq_true a4, a5,
    fun j hj => ?_, fun c hc => ?_⟩
  · have := allN_spec a2 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2.1, this.2.2.2⟩
  · have := allN_spec a6 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2.1, this.2.2⟩
  · have := allN_spec a7 c hc
    simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff] at this
    exact ⟨Nat.le_of_ble_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem invSK_spec {p r : Nat} (h : invSK p r = true) :
    C3 p ∧ C3 r ∧ invEqK 3850 12 (mask 12) (3850 * 12) p r = true := by
  unfold invSK at h
  simp only [bAnd_iff] at h
  exact h

theorem sylGens_eq : hsSylowGenTbls = [hsCentTbl 1, hsCentTbl 2, hsCentTbl 3, hsCentTbl 4] := rfl

theorem sG_parts {j : Nat} (hj : j < 4) :
    hsCentTbl (j + 1) = tabT (unpack 3850 12 (sG j)) ∧ C3 (sG j) :=
  ⟨CFSG.KD.HS3850.cent_tab (by omega), CFSG.KD.HS3850.cent_cn (by omega)⟩

theorem sG_tabs : TabsOK 3850 12 4 sG hsSylowGenTbls.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [getElem!_pos _ j (by simpa [sylGens_eq] using hj), List.getElem_toArray]
  have e : hsSylowGenTbls[j]'(by simpa [sylGens_eq] using hj) = hsCentTbl (j + 1) := by
    interval_cases j <;> rfl
  rw [e]
  exact sG_parts hj

theorem sG_inv : ∀ j < 4, invEqK 3850 12 (mask 12) (3850 * 12) (sG j) (sGI j) = true ∧
    canonK 3850 12 (mask 12) (3850 * 12) (sGI j) = true := fun j hj =>
  ⟨(invK_spec (sbase_parts.1 j hj)).2.2, (invK_spec (sbase_parts.1 j hj)).2.1⟩

theorem letters_ok : ∀ p ∈ harSPairs, (∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 4) ∧ ∀ l ∈ p.2, 1 ≤ l ∧ l ≤ 4 := by
  decide

theorem sWd_eq {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 4) :
    wordTbl 3850 hsSylowGenTbls wd = tabT (unpack 3850 12 (sWd wd)) ∧ C3 (sWd wd) :=
  wordTbl_unpack CFSG.KD.HS3850.hid CFSG.KD.HS3850.hidc fun l hl => by
    obtain ⟨h1, h2⟩ := hw l hl
    have e : hsSylowGenTbls.getD (l - 1) (idT 3850) = hsCentTbl l := by
      rw [sylGens_eq]
      rcases (by omega : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4) with rfl | rfl | rfl | rfl <;> rfl
    rw [e]
    exact ⟨CFSG.KD.HS3850.cent_tab (by omega), CFSG.KD.HS3850.cent_cn (by omega)⟩

theorem pair_eq {j : Nat} (hj : j < harSPairs.length) :
    wordTbl 3850 hsSylowGenTbls harSPairs[j].1 = tabT (unpack 3850 12 (sA j)) ∧ C3 (sA j) ∧
      wordTbl 3850 hsSylowGenTbls harSPairs[j].2 = tabT (unpack 3850 12 (sB j)) ∧ C3 (sB j) := by
  have hp : harSPairs.getD j ([], []) = harSPairs[j] := List.getD_eq_getElem _ _ _
  have hl := letters_ok _ (List.getElem_mem hj)
  obtain ⟨e1, c1⟩ := sWd_eq hl.1
  obtain ⟨e2, c2⟩ := sWd_eq hl.2
  unfold sA sB
  rw [hp]
  exact ⟨e1, c1, e2, c2⟩

theorem comm_eq {a b : Nat} (ha : invK a = true) (hb : invK b = true) :
    tComm 3850 (tabT (unpack 3850 12 a)) (tabT (unpack 3850 12 b)) = tabT (unpack 3850 12 (sComm a b)) ∧
      C3 (sComm a b) := by
  obtain ⟨ca, cai, -⟩ := invK_spec ha
  obtain ⟨cb, cbi, -⟩ := invK_spec hb
  obtain ⟨-, ia, -⟩ := perm_of ha
  obtain ⟨-, ib, -⟩ := perm_of hb
  unfold tComm sComm
  rw [ia, ib, compT_unpack ca cb, compT_unpack cai cbi,
    compT_unpack (CFSG.KC.BfsPin.canonK_pcomp ca cb) (CFSG.KC.BfsPin.canonK_pcomp cai cbi)]
  exact ⟨rfl, CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp ca cb)
    (CFSG.KC.BfsPin.canonK_pcomp cai cbi)⟩

theorem SD_tabs : TabsOK 3850 12 4 SD.GI harSCgens.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  have hj' : j < harSPairs.length := hj
  have e : harSCgens = harSPairs.map fun p =>
      tComm 3850 (wordTbl 3850 hsSylowGenTbls p.1) (wordTbl 3850 hsSylowGenTbls p.2) := rfl
  rw [getElem!_pos _ j (by simpa [e] using hj'), List.getElem_toArray]
  simp only [e, List.getElem_map]
  obtain ⟨e1, -, e2, -⟩ := pair_eq hj'
  obtain ⟨-, -, ia, ib⟩ := sbase_parts.2.1 j hj
  rw [e1, e2, (sbase_parts.2.2.2.2.1 j hj).1]
  exact comm_eq ia ib

theorem SD_G : ∀ j < 4, SD.G j = pidn 3850 12 := fun j hj => (sbase_parts.2.2.2.2.1 j hj).2.1

theorem SD_inv : ∀ j < 4, invEqK 3850 12 (mask 12) (3850 * 12) (SD.GI j) (SDI j) = true ∧
    canonK 3850 12 (mask 12) (3850 * 12) (SDI j) = true := fun j hj =>
  ⟨(invSK_spec (sbase_parts.2.2.2.2.1 j hj).2.2).2.2,
    (invSK_spec (sbase_parts.2.2.2.2.1 j hj).2.2).2.1⟩

theorem peD_all : ∀ k < 4, peD k = true := by
  intro k hk
  interval_cases k
  exacts [peD0, peD1, peD2, peD3]

theorem clD_all : ∀ k < 4, clD k = true := by
  intro k hk
  interval_cases k
  exacts [clD0, clD1, clD2, clD3]

theorem nqD_all : ∀ k < 4, nqD k = true := by
  intro k hk
  interval_cases k
  exacts [nqD0, nqD1, nqD2, nqD3]

theorem sDE : ∀ i < SD.cnt, penumPtK 3850 12 (mask 12) (3850 * 12) true SD.G SD.GI 4 SD.cnt SD.T
    SD.PL SD.POS SD.SRT SD.SRI i = true := by
  intro i hi
  have hc := sbase_parts.2.2.1
  have hk : i / 16 < 4 := by omega
  exact penumSl_spec (peD_all (i / 16) hk) i (by change 16 * (i / 16) ≤ i; omega)
    (by change i < 16 * (i / 16) + 16; omega) hi

theorem sDH : ∀ i < SD.cnt, hsortPtK 3850 12 (mask 12) SD.cnt SD.T SD.HS SD.HSI i = true := by
  intro i hi
  have hc := sbase_parts.2.2.1
  rw [← hsortPtKF_eq 3850 12 SD.cnt SD.T SD.HS SD.HSI i]
  exact slK_spec hsD0 i (by change 64 * 0 ≤ i; omega) (by change i < 64 * 0 + 64; omega) hi

theorem sDCl : ∀ c < SD.cnt * (4 + 4), findPtK SD.cnt SD.T
    (prodQK 3850 12 (mask 12) (4 + 4) SD.T (bothK 4 SD.GI SDI)) SDCl c = true := by
  intro c hc'
  have hc := sbase_parts.2.2.1
  have hk : c / 128 < 4 := by omega
  exact slK_spec (clD_all (c / 128) hk) c (by change 128 * (c / 128) ≤ c; omega)
    (by change c < 128 * (c / 128) + 128; omega) (by change c < SD.cnt * 8; omega)

theorem sDN : ∀ c < SD.cnt * 4, findPtK SD.cnt SD.T (conjQK 3850 12 (mask 12) 4 SD.T sG sGI) SDN c =
    true := by
  intro c hc'
  have hc := sbase_parts.2.2.1
  have hk : c / 64 < 4 := by omega
  exact slK_spec (nqD_all (c / 64) hk) c (by change 64 * (c / 64) ≤ c; omega)
    (by change c < 64 * (c / 64) + 64; omega) (by change c < Nat.mul SD.cnt 4; omega)

theorem harSOK_true :
    harSOK = true := by
  have hn := hnS
  obtain ⟨hgi, hw, hc, hh, -, hm⟩ := sbase_parts
  have he := enumOK_of hn SD_G SD_tabs SD_inv hh sDE sDH sDCl hc
  have hnm := normOK_of hn SD_G SD_tabs hh sDE sDH sG_tabs sG_inv sDN
  have hmul := mulH_sound hn SD_G SD_tabs hh sDE sDH
  have h1 : hsSylowGenTbls.all (fun g => permOK 3850 g && invOK 3850 g (invT 3850 g)) = true := by
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨j, hj, rfl, -⟩ := TabsOK_list sG_tabs hg
    obtain ⟨p1, -, p3⟩ := perm_of (hgi j hj)
    rw [p1, p3]
    rfl
  have h2 : harSPairs.all (fun p => hsSift (wordTbl 3850 hsSylowGenTbls p.1) &&
      hsSift (wordTbl 3850 hsSylowGenTbls p.2)) = true := by
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    have hj4 : j < 4 := hj
    obtain ⟨e1, c1, e2, c2⟩ := pair_eq hj
    obtain ⟨w1, w2, -, -⟩ := hw j hj4
    have hl : ∀ k < 8, ∀ x ∈ sdW.getD k [], x < 16 := by decide
    rw [CFSG.KD.HS3850.sift_word (hl _ (by omega)) e1 c1 w1,
      CFSG.KD.HS3850.sift_word (hl _ (by omega)) e2 c2 w2]
    rfl
  have h3 : harSCgens.all (permOK 3850) = true := by
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨j, hj, rfl, c⟩ := TabsOK_list SD_tabs hg
    exact permOK_unpack c (SD_inv j hj).1
  have hT : ∀ q < SD.cnt, C3 (SD.T q) := fun q hq => penumPt_canon (sDE q hq)
  have h6 : hsSylowGenTbls.all (fun g => hsSylowGenTbls.all fun h =>
      memT 3850 (mulClosureH 3850 harSCgens.toArray 200).1 (tComm 3850 g h)) = true := by
    rw [hmul.1, List.all_eq_true]
    intro g hg
    rw [List.all_eq_true]
    intro h hh'
    obtain ⟨a, ha, rfl, -⟩ := TabsOK_list sG_tabs hg
    obtain ⟨b, hb, rfl, -⟩ := TabsOK_list sG_tabs hh'
    obtain ⟨ec, cc⟩ := comm_eq (hgi a ha) (hgi b hb)
    have hc16 : 4 * a + b < 16 := by omega
    obtain ⟨hq, hv⟩ := hm (4 * a + b) hc16
    have ea : (4 * a + b) / 4 = a := by omega
    have eb : (4 * a + b) % 4 = b := by omega
    rw [ea, eb] at hv
    rw [ec]
    refine memT_of hq ?_
    rw [hv]
    exact tblEq_self cc
  unfold harSOK
  simp only []
  rw [h1, h2, h3, he, hnm, h6]
  rfl

end CFSG.KD.TwoHS

end
