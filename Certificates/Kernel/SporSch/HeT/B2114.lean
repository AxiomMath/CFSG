
module

public import Certificates.Kernel.SporSch.HeT.B2114K
public import Certificates.Kernel.SporSch.HeT.PtGlue
public import Certificates.Kernel.Sporadic.OddCore.Glue
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.HeAutKSound
public import CFSG.Certificates.Kernel.HeFixKSound
public import CFSG.Certificates.Kernel.PermToolSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeB14

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CertificateChecks.KernelSpor CertificateChecks.KernelLQT.He4148
open CertificateChecks.KernelSporSch.HeX14 CertificateChecks.KernelSporSch.HePt

theorem c0_ok {j : Nat} (hj : j < 9) : c0K j = true := by
  interval_cases j
  exacts [k00, k01, k02, k03, k04, k05, k06, k07, k08]

theorem c1_ok {j : Nat} (hj : j < 9) : c1K j = true := by
  interval_cases j
  exacts [k10, k11, k12, k13, k14, k15, k16, k17, k18]

theorem kT1s : invEqK 8330 14 (mask 14) (8330 * 14) T1 T1I = true ∧
    invEqK 8330 14 (mask 14) (8330 * 14) T1I T1 = true ∧
    sqIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) T1 = true ∧
    neIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) T1 = true ∧
    sqIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) (HeC.S 0) = true ∧
    neIdK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14) (HeC.S 0) = true ∧
    Nat.beq (C0 0) (HeC.S 0) = true ∧ Nat.beq (C1 0) T1 = true := by
  simpa only [bAnd_iff] using kT1

theorem kPs : szOK 8330 14 = true ∧
    allN 2 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LS 18 l) (LSI 18 l)) = true ∧
    allN 3 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LA l) (LAI l)) = true ∧
    allN 3 (fun l => permOK 8330 14 (mask 14) (8330 * 14) (LB l) (LBI l)) = true := by
  simpa only [bAnd_iff] using kP

theorem kLs : allN 9 (fun j => lettersK 3 (WD j)) = true ∧
    allN 9 (fun j => lettersK 3 (WD (Nat.add 9 j))) = true ∧ lettersK 2 (WD 18) = true := by
  simpa only [bAnd_iff] using kL

theorem gen_eq {k : Nat} (hk : k < 2) : heGen k = unpack 8330 14 (HeC.S k) := by
  have h := He2112.gen_eq k hk
  rw [heGenArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn] at h
  exact h

theorem get2 (a b : Array Nat) : #[a, b].size = 2 ∧ #[a, b][0]! = a ∧ #[a, b][1]! = b := by
  simp

theorem get3 (a b c : Array Nat) :
    #[a, b, c].size = 3 ∧ #[a, b, c][0]! = a ∧ #[a, b, c][1]! = b ∧ #[a, b, c][2]! = c := by
  simp

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem word_ok {j kS : Nat} (hj : j < 19) (hl : lettersK kS (WD j) = true) :
    wordEqK 8330 14 (mask 14) (pidn 8330 14) (LS j) (LSI j) kS (WD j) (V j 0) = true := by
  obtain ⟨h0, hlen, hc⟩ := kChunks j hj
  refine wordEqK_of_chunks kPs.1 hl hlen h0 fun c hcl => ?_
  obtain ⟨hg, hj', hc'⟩ := hc c hcl
  have h := HeB14K.all _ hg
  unfold gk at h
  rw [strictB_app, hj', hc'] at h
  exact h

theorem LS_lo {j : Nat} (hj : j < 9) : LS j = LA ∧ LSI j = LAI ∧ WD j = heInnerWords0.getD j [] := by
  have h1 : Nat.ble 9 j = false := by
    cases e : Nat.ble 9 j
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true e) (by omega)
  have h2 : Nat.blt j 9 = true := by
    rw [Nat.blt_eq]
    exact hj
  refine ⟨funext fun l => ?_, funext fun l => ?_, ?_⟩
  · unfold LS
    rw [h1]
  · unfold LSI
    rw [h1]
  · unfold WD
    rw [h2]

theorem LS_mid {j : Nat} (hj : j < 9) : LS (Nat.add 9 j) = LB ∧ LSI (Nat.add 9 j) = LBI ∧
    WD (Nat.add 9 j) = heInnerWords1.getD j [] := by
  have h1 : Nat.ble 9 (Nat.add 9 j) = true := Nat.ble_eq.mpr (by change 9 ≤ 9 + j; omega)
  have h3 : Nat.blt (Nat.add 9 j) 18 = true := by
    rw [Nat.blt_eq]
    change 9 + j < 18
    omega
  have h2 : Nat.blt (Nat.add 9 j) 9 = false := by
    cases e : Nat.blt (Nat.add 9 j) 9
    · rfl
    · exact absurd (Nat.blt_eq.mp e) (by change ¬ 9 + j < 9; omega)
  have h4 : Nat.sub (Nat.add 9 j) 9 = j := by
    change 9 + j - 9 = j
    omega
  refine ⟨funext fun l => ?_, funext fun l => ?_, ?_⟩
  · unfold LS
    rw [h1, h3]
  · unfold LSI
    rw [h1, h3]
  · unfold WD
    rw [h2, h3, h4]

theorem T1_eq : heT1Arr = unpack 8330 14 T1 := by
  obtain ⟨s, e0, e1⟩ := get2 (heGen 0) (heGen 1)
  have hS : heABArrs.size = 2 ∧ ∀ j < 2, heABArrs[j]! = unpack 8330 14 (LS 18 j) := by
    refine ⟨s, fun j hj => ?_⟩
    interval_cases j
    · exact e0.trans (gen_eq (by norm_num))
    · exact e1.trans (gen_eq (by norm_num))
  exact (wordEqK_sound hS kPs.2.1 (word_ok (j := 18) (by norm_num) kLs.2.2)).1

theorem T1_letters : lettersOK 2 heT1Word = true := by
  obtain ⟨s, e0, e1⟩ := get2 (heGen 0) (heGen 1)
  have hS : heABArrs.size = 2 ∧ ∀ j < 2, heABArrs[j]! = unpack 8330 14 (LS 18 j) := by
    refine ⟨s, fun j hj => ?_⟩
    interval_cases j
    · exact e0.trans (gen_eq (by norm_num))
    · exact e1.trans (gen_eq (by norm_num))
  exact (wordEqK_sound hS kPs.2.1 (word_ok (j := 18) (by norm_num) kLs.2.2)).2

theorem LA_eq {l : Nat} (hl : l < 3) : heInnerLetters0[l]! = unpack 8330 14 (LA l) := by
  obtain ⟨-, e0, e1, e2⟩ := get3 (heGen 0) (heGen 1) (heGen 0)
  interval_cases l
  · exact e0.trans (gen_eq (by norm_num))
  · exact e1.trans (gen_eq (by norm_num))
  · exact e2.trans (gen_eq (by norm_num))

theorem LB_eq {l : Nat} (hl : l < 3) : heInnerLetters1[l]! = unpack 8330 14 (LB l) := by
  obtain ⟨-, e0, e1, e2⟩ := get3 (heGen 0) (heGen 1) heT1Arr
  interval_cases l
  · exact e0.trans (gen_eq (by norm_num))
  · exact e1.trans (gen_eq (by norm_num))
  · exact e2.trans T1_eq

theorem c0_parts {j : Nat} (hj : j < 9) :
    invEqK 8330 14 (mask 14) (8330 * 14) (C0 j) (C0I j) = true ∧
    invEqK 8330 14 (mask 14) (8330 * 14) (C0I j) (C0 j) = true ∧
    commK 8330 14 (mask 14) (8330 * 14) (C0 j) (HeC.S 0) = true ∧
    allN 240 (fun k => Nat.beq (pg 14 (mask 14) (C0 j) (nget D0 k))
      (nget D0 (pg 8 (mask 8) (X0Q.S j) k))) = true := by
  simpa only [c0K, bAnd_iff] using c0_ok hj

theorem c1_parts {j : Nat} (hj : j < 9) :
    invEqK 8330 14 (mask 14) (8330 * 14) (C1 j) (C1I j) = true ∧
    invEqK 8330 14 (mask 14) (8330 * 14) (C1I j) (C1 j) = true ∧
    commK 8330 14 (mask 14) (8330 * 14) (C1 j) T1 = true ∧
    allN 42 (fun k => Nat.beq (pg 14 (mask 14) (C1 j) (nget D1 k))
      (nget D1 (pg 6 (mask 6) (X1Q.S j) k))) = true := by
  simpa only [c1K, bAnd_iff] using c1_ok hj

theorem C0_word {j : Nat} (hj : j < 9) : heInnerC0 j = unpack 8330 14 (C0 j) ∧
    lettersOK 3 (heInnerWords0.getD j []) = true := by
  obtain ⟨e1, e2, e3⟩ := LS_lo hj
  have hl : lettersK 3 (WD j) = true := allN_spec kLs.1 j hj
  have h := word_ok (by omega) hl
  rw [e1, e2, e3] at h
  exact wordEqK_sound ⟨rfl, fun _ hl => LA_eq hl⟩ kPs.2.2.1 h

theorem C1_word {j : Nat} (hj : j < 9) : heInnerC1 j = unpack 8330 14 (C1 j) ∧
    lettersOK 3 (heInnerWords1.getD j []) = true := by
  obtain ⟨e1, e2, e3⟩ := LS_mid hj
  have hl : lettersK 3 (WD (Nat.add 9 j)) = true := allN_spec kLs.2.1 j hj
  have h := word_ok (by change 9 + j < 19; omega) hl
  rw [e1, e2, e3] at h
  exact wordEqK_sound ⟨rfl, fun _ hl => LB_eq hl⟩ kPs.2.2.2 h

theorem d0_eq : heDelta0.toList = D0 := by decide +kernel

theorem d1_eq : heDelta1.toList = D1 := by decide +kernel

theorem d0_len : D0.length = 240 := rfl

theorem d1_len : D1.length = 42 := rfl

theorem d0_inc : ∀ k < 240 - 1, nget D0 k < nget D0 (k + 1) := by decide +kernel

theorem d1_inc : ∀ k < 42 - 1, nget D1 k < nget D1 (k + 1) := by decide +kernel

theorem d0_lt : ∀ x ∈ D0, x < 8330 := by decide +kernel

theorem d1_lt : ∀ x ∈ D1, x < 8330 := by decide +kernel

theorem big : lettersOK 2 heT1Word = true ∧ permChk 8330 heT1Arr = true ∧
    eqA 8330 (compA 8330 heT1Arr heT1Arr) (idA 8330) = true ∧
    eqA 8330 heT1Arr (idA 8330) = false ∧
    eqA 8330 (compA 8330 (heGen 0) (heGen 0)) (idA 8330) = true ∧
    eqA 8330 (heGen 0) (idA 8330) = false ∧
    heInnerWords0.length = 9 ∧ heInnerWords1.length = 9 ∧
    (∀ j < 9, lettersOK 3 (heInnerWords0.getD j []) = true ∧ permChk 8330 (heInnerC0 j) = true ∧
      eqA 8330 (compA 8330 (heInnerC0 j) (heGen 0)) (compA 8330 (heGen 0) (heInnerC0 j)) = true ∧
      permChk 240 (heInnerSigma0.getD j #[]) = true ∧
      agreeOK 240 (heInnerC0 j) heDelta0 (heInnerSigma0.getD j #[]) = true) ∧
    (∀ j < 9, lettersOK 3 (heInnerWords1.getD j []) = true ∧ permChk 8330 (heInnerC1 j) = true ∧
      eqA 8330 (compA 8330 (heInnerC1 j) heT1Arr) (compA 8330 heT1Arr (heInnerC1 j)) = true ∧
      permChk 42 (heInnerSigma1.getD j #[]) = true ∧
      agreeOK 42 (heInnerC1 j) heDelta1 (heInnerSigma1.getD j #[]) = true) ∧
    incListOK 8330 240 heDelta0 = true ∧ fixesOK 240 (heGen 0) heDelta0 = true ∧
    incListOK 8330 42 heDelta1 = true ∧ fixesOK 42 heT1Arr heDelta1 = true ∧
    eqA 8330 (heInnerC0 0) (heGen 0) = true ∧ eqA 8330 (heInnerC1 0) heT1Arr = true := by
  obtain ⟨hi1, hi2, hsq, hne, hsq0, hne0, he0, he1⟩ := kT1s
  have g0 := gen_eq (k := 0) (by norm_num)
  have hfix : allN 240 (fun k => Nat.beq (pg 14 (mask 14) (HeC.S 0) (nget D0 k)) (nget D0 k)) = true ∧
      allN 42 (fun k => Nat.beq (pg 14 (mask 14) T1 (nget D1 k)) (nget D1 k)) = true := by
    simpa only [bAnd_iff] using kFix
  obtain ⟨hf0, hf1⟩ := hfix
  refine ⟨T1_letters, perm_of T1_eq hi1 hi2, ?_, ?_, ?_, ?_, rfl, rfl, fun j hj => ?_,
    fun j hj => ?_, inc_ok d0_eq d0_len d0_lt d0_inc, fixes_ok d0_eq d0_len g0 d0_lt hf0,
    inc_ok d1_eq d1_len d1_lt d1_inc, fixes_ok d1_eq d1_len T1_eq d1_lt hf1, ?_, ?_⟩
  · rw [T1_eq]
    exact sqIdK_sound hsq
  · rw [T1_eq]
    exact neIdK_sound hne
  · rw [g0]
    exact sqIdK_sound hsq0
  · rw [g0]
    exact neIdK_sound hne0
  · obtain ⟨hc1, hc2, hcc, hca⟩ := c0_parts hj
    obtain ⟨ce, cl⟩ := C0_word hj
    obtain ⟨σe, σp, -, -⟩ := bind_facts (atX0 hj)
    refine ⟨cl, perm_of ce hc1 hc2, ?_, σp, ?_⟩
    · rw [ce, g0]
      exact commK_sound hcc
    · exact agree_ok d0_eq d0_len ce σe (atX0 hj).2.2.2.1 d0_lt hca
  · obtain ⟨hc1, hc2, hcc, hca⟩ := c1_parts hj
    obtain ⟨ce, cl⟩ := C1_word hj
    obtain ⟨σe, σp, -, -⟩ := bind_facts (atX1 hj)
    refine ⟨cl, perm_of ce hc1 hc2, ?_, σp, ?_⟩
    · rw [ce, T1_eq]
      exact commK_sound hcc
    · exact agree_ok d1_eq d1_len ce σe (atX1 hj).2.2.2.1 d1_lt hca
  · rw [(C0_word (j := 0) (by norm_num)).1, g0, Nat.eq_of_beq_eq_true he0]
    exact eqK_sound (Nat.beq_refl _)
  · rw [(C1_word (j := 0) (by norm_num)).1, T1_eq, Nat.eq_of_beq_eq_true he1]
    exact eqK_sound (Nat.beq_refl _)

end CertificateChecks.KernelSporSch.HeB14

end
