module

public import Certificates.Kernel.SporSch.HeT.W2117K
public import Certificates.Kernel.SporSch.HeT.Q2117
public import Certificates.Kernel.SporSch.HeT.Out2116
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeW17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch CertificateChecks.KernelLQT.He4148
open CertificateChecks.KernelSporSch.HePt

theorem kUIs : invEqK 8330 14 (mask 14) (8330 * 14) U UI = true ∧
    invEqK 8330 14 (mask 14) (8330 * 14) UI U = true := by
  simpa only [bAnd_iff] using kUI

theorem kPs : szOK 8330 14 = true ∧
    allN 3 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LS 0 l) (LSI 0 l)) = true ∧
    allN 2 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LS 2 l) (LSI 2 l)) = true := by
  simpa only [bAnd_iff] using kP

theorem kLs : lettersK 3 (WD 0) = true ∧ lettersK 3 (WD 1) = true ∧
    allN 3 (fun j => lettersK 2 (WD (Nat.add 2 j))) = true := by
  simpa only [bAnd_iff] using kL

theorem kFixs : Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 U) 98 = true ∧
    allN 98 (fun k => Nat.beq (pg 14 (mask 14) U (nget FU k)) (nget FU k)) = true := by
  simpa only [bAnd_iff] using kFix

theorem c_parts {j : Nat} (hj : j < 2) :
    invEqK 8330 14 (mask 14) (8330 * 14) (C j) (CI j) = true ∧
    invEqK 8330 14 (mask 14) (8330 * 14) (CI j) (C j) = true ∧
    commK 8330 14 (mask 14) (8330 * 14) (C j) U = true ∧
    allN 98 (fun k => Nat.beq (pg 14 (mask 14) (C j) (nget FU k))
      (nget FU (pg 7 (mask 7) (HeQ17.QC.S j) k))) = true := by
  have h : cK j = true := by
    interval_cases j
    exacts [kC0, kC1]
  simpa only [cK, bAnd_iff] using h

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem word_ok {j kS : Nat} (hj : j < 5) (hl : lettersK kS (WD j) = true) :
    wordEqK 8330 14 (mask 14) (pidn 8330 14) (LS j) (LSI j) kS (WD j) (V j 0) = true := by
  obtain ⟨h0, hlen, hc⟩ := kChunks j hj
  refine wordEqK_of_chunks kPs.1 hl hlen h0 fun c hcl => ?_
  obtain ⟨hg, hj', hc'⟩ := hc c hcl
  have h := HeW17K.all _ hg
  unfold gk at h
  rw [strictB_app, hj', hc'] at h
  exact h

theorem U_eq : heUArr = unpack 8330 14 U := by
  rw [heUArr, HeO16.R_eq, (HeO16.pow_unpack HeO16.kCanon 5).1, Nat.eq_of_beq_eq_true kU5]

theorem get2 (a b : Array Nat) : #[a, b].size = 2 ∧ #[a, b][0]! = a ∧ #[a, b][1]! = b := by
  simp

theorem get3 (a b c : Array Nat) :
    #[a, b, c].size = 3 ∧ #[a, b, c][0]! = a ∧ #[a, b, c][1]! = b ∧ #[a, b, c][2]! = c := by
  simp

theorem LC_eq {l : Nat} (hl : l < 3) : heLetterArrs[l]! = unpack 8330 14 (LS 0 l) := by
  obtain ⟨-, e0, e1, e2⟩ := get3 (heGen 0) (heGen 1) heUArr
  interval_cases l
  · exact e0.trans (HeO16.gen_eq 0 (by norm_num))
  · exact e1.trans (HeO16.gen_eq 1 (by norm_num))
  · exact e2.trans U_eq

theorem C_word {j : Nat} (hj : j < 2) : heCArrs[j]! = unpack 8330 14 (C j) ∧
    lettersOK 3 (WD j) = true := by
  obtain ⟨-, e0, e1⟩ := get2 (wordA 8330 heLetterArrs (heLetterArrs.map (invCand 8330)) heCentW1)
    (wordA 8330 heLetterArrs (heLetterArrs.map (invCand 8330)) heCentW2)
  interval_cases j
  · have h : wordEqK 8330 14 (mask 14) (pidn 8330 14) (LS 0) (LSI 0) 3 heCentW1 (C 0) = true :=
      word_ok (j := 0) (by norm_num) kLs.1
    have := wordEqK_sound ⟨rfl, fun _ hl => LC_eq hl⟩ kPs.2.1 h
    exact ⟨e0.trans this.1, this.2⟩
  · have h : wordEqK 8330 14 (mask 14) (pidn 8330 14) (LS 1) (LSI 1) 3 heCentW2 (C 1) = true :=
      word_ok (j := 1) (by norm_num) kLs.2.1
    have := wordEqK_sound ⟨rfl, fun _ hl => LC_eq hl⟩ kPs.2.1 h
    exact ⟨e1.trans this.1, this.2⟩

theorem LD_eq {l : Nat} (hl : l < 2) : heCArrs[l]! = unpack 8330 14 (LS 2 l) := by
  interval_cases l
  · exact (C_word (j := 0) (by norm_num)).1
  · exact (C_word (j := 1) (by norm_num)).1

theorem D_word {j : Nat} (hj : j < 3) : heDArr j = unpack 8330 14 (D j) ∧
    lettersOK 2 (heDerivedV.getD j []) = true := by
  have hS : heCArrs.size = 2 ∧ ∀ l < 2, heCArrs[l]! = unpack 8330 14 (LS 2 l) :=
    ⟨rfl, fun _ hl => LD_eq hl⟩
  interval_cases j
  · have h : wordEqK 8330 14 (mask 14) (pidn 8330 14) (LS 2) (LSI 2) 2 (heDerivedV.getD 0 [])
        (D 0) = true := word_ok (j := 2) (by norm_num) (allN_spec kLs.2.2 0 (by norm_num))
    exact wordEqK_sound hS kPs.2.2 h
  · have h : wordEqK 8330 14 (mask 14) (pidn 8330 14) (LS 2) (LSI 2) 2 (heDerivedV.getD 1 [])
        (D 1) = true := word_ok (j := 3) (by norm_num) (allN_spec kLs.2.2 1 (by norm_num))
    exact wordEqK_sound hS kPs.2.2 h
  · have h : wordEqK 8330 14 (mask 14) (pidn 8330 14) (LS 2) (LSI 2) 2 (heDerivedV.getD 2 [])
        (D 2) = true := word_ok (j := 4) (by norm_num) (allN_spec kLs.2.2 2 (by norm_num))
    exact wordEqK_sound hS kPs.2.2 h

theorem bind_all {j : Nat} (hj : j < 2) :
    ∀ x < 8330, bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (nget NF j) (C j) x = true := by
  intro x hx
  have hg : 10 * j + x / 833 < 20 := by omega
  have h := allN_spec (HeW17B.all _ hg) (x % 833) (Nat.mod_lt _ (by norm_num))
  have e1 : Nat.div (10 * j + x / 833) 10 = j := by
    change (10 * j + x / 833) / 10 = j
    omega
  have e2 : Nat.add (Nat.mul (Nat.mod (10 * j + x / 833) 10) 833) (x % 833) = x := by
    change (10 * j + x / 833) % 10 * 833 + x % 833 = x
    have : (10 * j + x / 833) % 10 = x / 833 := by omega
    rw [this]
    exact Nat.div_add_mod' x 833
  rwa [e1, e2] at h

theorem C_rep {j : Nat} (hj : j < 2) : Rep 8330 (unpack 8330 14 (C j)) (HeO16.E (nget NF j)) :=
  HeO16.rep_of_repF (bind5_spec HeTc.tc (allN_spec kNF j hj) (bind_all hj))

theorem C_sift {j : Nat} (hj : j < 2) :
    siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0 heCArrs[j]! = true := by
  rw [(C_word hj).1, mem_heP_iff_siftA (C_rep hj), heP_eq_originalSubgroup]
  exact HeO16.E_mem (allN_spec kNF j hj)

theorem big : lettersOK 3 heCentW1 = true ∧
    lettersOK 3 heCentW2 = true ∧
    (∀ j < 3, lettersOK 2 (heDerivedV.getD j []) = true) ∧ permChk 8330 heUArr = true ∧
    (∀ j < 2, permChk 8330 heCArrs[j]! = true) ∧
    (∀ j < 2, eqA 8330 (compA 8330 heCArrs[j]! heUArr) (compA 8330 heUArr heCArrs[j]!) = true) ∧
    (∀ j < 2, siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0
      heCArrs[j]! = true) ∧
    fixListOK 8330 98 heUArr heFixU = true ∧ permChk 98 heSigma1 = true ∧
    permChk 98 heSigma2 = true ∧ agreeOK 98 heCArrs[0]! heFixU heSigma1 = true ∧
    agreeOK 98 heCArrs[1]! heFixU heSigma2 = true ∧
    (∀ j < 3, permChk 98 (heTauArr j) = true ∧
      agreeOK 98 (heDArr j) heFixU (heTauArr j) = true) := by
  obtain ⟨fe, fl, flt, finc⟩ := kF
  obtain ⟨fc, ff⟩ := kFixs
  have s0 := HeQ17.atQC (j := 0) (by norm_num)
  have s1 := HeQ17.atQC (j := 1) (by norm_num)
  have a0 := (c_parts (j := 0) (by norm_num)).2.2.2
  have a1 := (c_parts (j := 1) (by norm_num)).2.2.2
  refine ⟨(C_word (j := 0) (by norm_num)).2, (C_word (j := 1) (by norm_num)).2,
    fun j hj => (D_word hj).2, perm_of U_eq kUIs.1 kUIs.2,
    fun j hj => perm_of (C_word hj).1 (c_parts hj).1 (c_parts hj).2.1, fun j hj => ?_,
    fun j hj => C_sift hj, fixList_ok fe fl U_eq flt finc ff (Nat.eq_of_beq_eq_true fc),
    (bind_facts s0).2.1, (bind_facts s1).2.1,
    agree_ok fe fl (C_word (j := 0) (by norm_num)).1 (bind_facts s0).1 s0.2.2.2.1 flt a0,
    agree_ok fe fl (C_word (j := 1) (by norm_num)).1 (bind_facts s1).1 s1.2.2.2.1 flt a1,
    fun j hj => ⟨perm_of (HeQ17.tau_eq hj) (HeQ17.tau_parts hj).2.1 (HeQ17.tau_parts hj).2.2.1,
      agree_ok fe fl (D_word hj).1 (HeQ17.tau_eq hj) (HeQ17.tau_parts hj).2.2.2.1 flt
        (allN_spec kD j hj)⟩⟩
  rw [(C_word hj).1, U_eq]
  exact commK_sound (c_parts hj).2.2.1

end CertificateChecks.KernelSporSch.HeW17

end
