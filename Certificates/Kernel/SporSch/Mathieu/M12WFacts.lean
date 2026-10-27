module

public import Certificates.Kernel.SporSch.Mathieu.M12WChecks
public import Certificates.Kernel.SporSch.Mathieu.M12Facts
public import CFSG.Certificates.Kernel.SporSch.MathieuOddGlue
public import CFSG.Certificates.Kernel.SporSch.CF67GenSound
public import CFSG.Certificates.Kernel.SporSch.ChainKClassEq
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Abs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12W

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.KS.SporSch.OddWit CFSG.KS.SporSch CFSG.KS.SporSch.CF67K
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M12OC
open CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem hn : (12 : ℕ) < 2 ^ 32 := by norm_num

theorem valid : ValidSchreier m12Certificate := chainK_valid chainQ (by decide) (by decide)

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem prep_word {wd : List ℤ} {P : ℕ} (h : bAnd(abOK wd, Nat.beq (abWordK 12 4 (mask 4)
    (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1) wd) P) = true) :
    PRep 12 4 P (evalCodes [m12gA, m12gB] wd) :=
  prep_of_imageList (img_word (and_of_bAnd h).1 (and_of_bAnd h).2)

theorem orig_eq : m12Certificate.originalSubgroup =
    Subgroup.closure ({m12gA, m12gB} : Set (Equiv.Perm (Fin 12))) := by
  rw [m12Certificate, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem gens_mem : ∀ g ∈ [m12gA, m12gB],
    g ∈ Subgroup.closure ({m12gA, m12gB} : Set (Equiv.Perm (Fin 12))) := by
  intro g hg
  apply Subgroup.subset_closure
  simpa using hg

theorem word_mem (wd : List ℤ) : evalCodes [m12gA, m12gB] wd ∈ m12Certificate.originalSubgroup := by
  rw [orig_eq]
  exact evalCodes_mem _ gens_mem wd

theorem hord : m12Certificate.orderCertificate = 95040 :=
  (chainK_check (by decide) (by decide) chainQ).2.trans (by decide)

abbrev ps : List (Equiv.Perm (Fin 12)) := Certificates.CF67.M12.pw.map (evalCodes [m12gA, m12gB])

abbrev es : List (Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) :=
  Certificates.CF67.M12.ew.map fun e => (evalCodes [m12gA, m12gB] e.1, evalCodes [m12gA, m12gB] e.2)

theorem es_get (e : ℕ) : es.getD e (1, 1) =
    (evalCodes [m12gA, m12gB] (Certificates.CF67.M12.ew.getD e ([], [])).1,
      evalCodes [m12gA, m12gB] (Certificates.CF67.M12.ew.getD e ([], [])).2) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Certificates.CF67.M12.ew[e]? <;> rfl

theorem hP : ∀ i < 27, PRep 12 4 (PL.getD i 0) (ps.getD i 1) ∧ PL.getD i 0 >>> (12 * 4) = 0 := by
  intro i hi
  rw [getD_map_eval]
  exact ⟨prep_word (allN_spec bP i hi), Nat.eq_of_beq_eq_true (allN_spec shr.1 i hi)⟩

theorem pE1 (e : ℕ) (he : e < 4) : PRep 12 4 (E1L.getD e 0) (es.getD e (1, 1)).1 := by
  rw [es_get]
  exact prep_word (allN_spec bE1 e he)

theorem pE2 (e : ℕ) (he : e < 4) : PRep 12 4 (E2L.getD e 0) (es.getD e (1, 1)).2 := by
  rw [es_get]
  exact prep_word (allN_spec bE2 e he)

theorem hE : ∀ e < 4, PRep 12 4 (E1L.getD e 0) (es.getD e (1, 1)).1 ∧ E1L.getD e 0 >>> (12 * 4) = 0 ∧
    PRep 12 4 (E2L.getD e 0) (es.getD e (1, 1)).2 ∧ E2L.getD e 0 >>> (12 * 4) = 0 := by
  intro e he
  have h := and_of_bAnd (allN_spec shr.2 e he)
  exact ⟨pE1 e he, Nat.eq_of_beq_eq_true h.1, pE2 e he, Nat.eq_of_beq_eq_true h.2⟩

abbrev hGens0 : List (Equiv.Perm (Fin 12)) := MathieuC3.m12Words0.map (evalCodes [m12gA, m12gB])

abbrev hGens1 : List (Equiv.Perm (Fin 12)) := MathieuC3.m12Words1.map (evalCodes [m12gA, m12gB])

theorem chainH0 : ChainK 12 4 hGens0 MathieuC3.m12ChainWords0 (#v[2, 3] : Vector (Fin 12) 2)
    M12CH0.S M12CH0.SI M12CH0.LR M12CH0.TR M12CH0.TRI 5 M12CH0.BP 1 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M12CH0.head,
    M12CH0.hl, by norm_num, M12CH0.hs⟩
  have hj4 : j < 4 := by simpa [hGens0, MathieuC3.m12Words0] using hj
  rw [getD_map_eval]
  have h := allN_spec bH0 j hj4
  exact img_word (and_of_bAnd h).1 (and_of_bAnd h).2

theorem chainH1 : ChainK 12 4 hGens1 MathieuC3.m12ChainWords1 (#v[2, 3] : Vector (Fin 12) 2)
    M12CH1.S M12CH1.SI M12CH1.LR M12CH1.TR M12CH1.TRI 6 M12CH1.BP 1 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M12CH1.head,
    M12CH1.hl, by norm_num, M12CH1.hs⟩
  have hj4 : j < 4 := by simpa [hGens1, MathieuC3.m12Words1] using hj
  rw [getD_map_eval]
  have h := allN_spec bH1 j hj4
  exact img_word (and_of_bAnd h).1 (and_of_bAnd h).2

abbrev HQ0 : RawSchreierDatum 12 :=
  certificate (by decide) hGens0 MathieuC3.m12ChainWords0 #v[2, 3] (by decide)

abbrev HQ1 : RawSchreierDatum 12 :=
  certificate (by decide) hGens1 MathieuC3.m12ChainWords1 #v[2, 3] (by decide)

theorem H0_le : HQ0.originalSubgroup ≤ m12Certificate.originalSubgroup ⊓
    Subgroup.centralizer ({(es.getD 0 (1, 1)).1} : Set (Equiv.Perm (Fin 12))) := by
  rw [certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ hGens0 := hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  have hj4 : j < 4 := by simpa [hGens0, MathieuC3.m12Words0] using hj
  have pg : PRep 12 4 (M12CH0.S j) hGens0[j] := by
    have := prep_of_imageList (chainH0.2.2.2.1 j hj)
    rwa [List.getD_eq_getElem _ _ hj] at this
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 (mul_eq_of szOK' pg (pE1 0 (by norm_num))
    (pE1 0 (by norm_num)) pg (allN_spec hComm0 j hj4))⟩
  rw [List.getElem_map]
  exact word_mem _

theorem H1_le : HQ1.originalSubgroup ≤ m12Certificate.originalSubgroup ⊓
    Subgroup.centralizer ({(es.getD 1 (1, 1)).1} : Set (Equiv.Perm (Fin 12))) := by
  rw [certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ hGens1 := hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  have hj4 : j < 4 := by simpa [hGens1, MathieuC3.m12Words1] using hj
  have pg : PRep 12 4 (M12CH1.S j) hGens1[j] := by
    have := prep_of_imageList (chainH1.2.2.2.1 j hj)
    rwa [List.getD_eq_getElem _ _ hj] at this
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 (mul_eq_of szOK' pg (pE1 1 (by norm_num))
    (pE1 1 (by norm_num)) pg (allN_spec hComm1 j hj4))⟩
  rw [List.getElem_map]
  exact word_mem _

theorem card_H0 : Nat.card HQ0.originalSubgroup = 54 :=
  (card_group chainH0 (by decide) (by decide)).trans (Nat.eq_of_beq_eq_true hOrd.1)

theorem card_H1 : Nat.card HQ1.originalSubgroup = 54 :=
  (card_group chainH1 (by decide) (by decide)).trans (Nat.eq_of_beq_eq_true hOrd.2)

theorem card_C0 : Nat.card ↥(m12Certificate.originalSubgroup ⊓
    Subgroup.centralizer ({(es.getD 0 (1, 1)).1} : Set (Equiv.Perm (Fin 12)))) = 54 :=
  (card_centralizer_eq chainQ (by decide) (by decide) (by norm_num) (pE1 0 (by norm_num))).trans
    (Nat.eq_of_beq_eq_true cent0)

theorem card_C1 : Nat.card ↥(m12Certificate.originalSubgroup ⊓
    Subgroup.centralizer ({(es.getD 1 (1, 1)).1} : Set (Equiv.Perm (Fin 12)))) = 54 :=
  (card_centralizer_eq chainQ (by decide) (by decide) (by norm_num) (pE1 1 (by norm_num))).trans
    (Nat.eq_of_beq_eq_true cent1)

theorem H0_eq : HQ0.originalSubgroup = m12Certificate.originalSubgroup ⊓
    Subgroup.centralizer ({(es.getD 0 (1, 1)).1} : Set (Equiv.Perm (Fin 12))) :=
  Subgroup.eq_of_le_of_card_ge H0_le (by rw [card_H0, card_C0])

theorem H1_eq : HQ1.originalSubgroup = m12Certificate.originalSubgroup ⊓
    Subgroup.centralizer ({(es.getD 1 (1, 1)).1} : Set (Equiv.Perm (Fin 12))) :=
  Subgroup.eq_of_le_of_card_ge H1_le (by rw [card_H1, card_C1])

theorem hel0 : ∀ g ∈ HQ0.originalSubgroup, g * (es.getD 0 (1, 1)).2 = (es.getD 0 (1, 1)).2 * g →
    g ^ 27 = 1 := by
  intro g hg hgb
  obtain ⟨j, hj, rfl⟩ := (mem_group_iff chainH0 (by decide) (by decide) _).1 hg
  have hj' : j < 54 := by
    have := Nat.eq_of_beq_eq_true hOrd.1
    omega
  have pE := prep_elemK chainH0 j
  have h := allN_spec elems0 j hj'
  unfold powCommK at h
  rw [beq_pcomp_iff hn (by norm_num) pE (pE2 0 (by norm_num)) (pE2 0 (by norm_num)) pE,
    decide_eq_true hgb] at h
  exact pow_eq_one_of szOK' pE (by simpa using h)

theorem hel1 (e : ℕ) (he : e < 4) (he1 : 1 ≤ e)
    (hc : allN 54 (fun j => powCommK 12 4 (E2L.getD e 0) 27
      (elemK 12 4 (mask 4) (12 * 4) (pidn 12 4) M12CH1.LR M12CH1.TR 2 j)) = true) :
    ∀ g ∈ HQ1.originalSubgroup, g * (es.getD e (1, 1)).2 = (es.getD e (1, 1)).2 * g →
      g ^ 27 = 1 := by
  intro g hg hgb
  obtain ⟨j, hj, rfl⟩ := (mem_group_iff chainH1 (by decide) (by decide) _).1 hg
  have hj' : j < 54 := by
    have := Nat.eq_of_beq_eq_true hOrd.2
    omega
  have pE := prep_elemK chainH1 j
  have h := allN_spec hc j hj'
  unfold powCommK at h
  rw [beq_pcomp_iff hn (by norm_num) pE (pE2 e he) (pE2 e he) pE, decide_eq_true hgb] at h
  exact pow_eq_one_of szOK' pE (by simpa using h)

theorem e1_eq (e : ℕ) (he : e < 4) (he1 : 1 ≤ e) : (es.getD e (1, 1)).1 = (es.getD 1 (1, 1)).1 := by
  rw [es_get, es_get]
  interval_cases e <;> rfl

theorem pair_ok (e : ℕ) (he : e < 4) :
    ∀ T ∈ Certificates.CF67.commAllT 12 (levelTables m12Certificate)
      (toTable (es.getD e (1, 1)).1) (toTable (es.getD e (1, 1)).2), powFixW 12 [T] 27 = true := by
  rcases Nat.eq_zero_or_pos e with rfl | he1
  · exact commAll_pow hn valid H0_eq.symm.le hel0
  · have hc : allN 54 (fun j => powCommK 12 4 (E2L.getD e 0) 27
        (elemK 12 4 (mask 4) (12 * 4) (pidn 12 4) M12CH1.LR M12CH1.TR 2 j)) = true := by
      interval_cases e
      · exact elems1
      · exact elems2
      · exact elems3
    rw [e1_eq e he he1]
    exact commAll_pow hn valid H1_eq.symm.le (hel1 e he he1 hc)

theorem cf67 : Certificates.CF67.M12.m12CF67OK = true := by
  unfold Certificates.CF67.M12.m12CF67OK Certificates.CF67.cf67GenOK Certificates.CF67.cf67GenOKT
  have eP : (Certificates.CF67.M12.pw.map fun w => toTable (evalCodes [m12gA, m12gB] w)) =
      ps.map toTable := by
    simp [ps]
  have eE : (Certificates.CF67.M12.ew.map fun e =>
      (toTable (evalCodes [m12gA, m12gB] e.1), toTable (evalCodes [m12gA, m12gB] e.2))) =
      es.map fun e => (toTable e.1, toTable e.2) := by
    simp [es]
  rw [eP, eE]
  have lP : ps.length = 27 := by
    rw [List.length_map]
    rfl
  have lE : es.length = 4 := by
    rw [List.length_map]
    rfl
  obtain ⟨h1, h2, h3⟩ := sylK_sound szOK' (m := 27) (c := 4) lP lE hP hE syl
  simp only [Bool.and_eq_true, h1, h2, h3, and_true, true_and]
  refine ⟨⟨by rw [List.length_map, lP]; rfl, ?_⟩, ?_⟩
  · rw [hord]
    decide
  · rw [List.all_eq_true]
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hq
    have he4 : e < 4 := lE ▸ he
    rw [← List.getD_eq_getElem _ (1, 1) he, List.all_eq_true]
    have e27 : (2 : ℕ) ^ 0 * 3 ^ 3 = 27 := by norm_num
    rw [e27]
    exact pair_ok e he4

end CertificateChecks.KernelSporSch.M12W

end
