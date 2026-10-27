module

public import Certificates.Kernel.SporSch.Mathieu.M22WChecks
public import Certificates.Kernel.SporSch.Mathieu.M22OFacts
public import CFSG.Certificates.Kernel.SporSch.MathieuOddGlue
public import CFSG.Certificates.Kernel.SporSch.ChainKClassEq
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Th.KernelPlanes
public import CFSG.Sporadic.Th.Local
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Abs
public import CFSG.Sporadic.ThSchreier.AutCore

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22W

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.KS.SporSch.OddWit CFSG.KS.SporSch
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M22OC
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 Certificates.Odd87F3 CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem hn : (22 : ℕ) < 2 ^ 32 := by norm_num

theorem valid : ValidSchreier m22Certificate := chainK_valid chainQ (by decide) (by decide)

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem prep_word {wd : List ℤ} {P : ℕ} (h : bAnd(abOK wd, Nat.beq (abWordK 22 5 (mask 5)
    (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) wd) P) = true) :
    PRep 22 5 P (evalCodes [m22gA, m22gB] wd) :=
  prep_of_imageList (img_word (and_of_bAnd h).1 (and_of_bAnd h).2)

theorem orig_eq : m22Certificate.originalSubgroup =
    Subgroup.closure ({m22gA, m22gB} : Set (Equiv.Perm (Fin 22))) := by
  rw [m22Certificate, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem pAc : PRep 22 5 (packL 5 tA) m22gA := by
  rw [tA_eq]
  exact (prep_packL (by norm_num)).1

theorem pBc : PRep 22 5 (packL 5 tB) m22gB := by
  rw [tB_eq]
  exact (prep_packL (by norm_num)).1

theorem gens_mem : ∀ g ∈ [m22gA, m22gB],
    g ∈ Subgroup.closure ({m22gA, m22gB} : Set (Equiv.Perm (Fin 22))) := by
  intro g hg
  apply Subgroup.subset_closure
  simpa using hg

theorem word_mem (wd : List ℤ) : evalCodes [m22gA, m22gB] wd ∈ m22Certificate.originalSubgroup := by
  rw [orig_eq]
  exact evalCodes_mem _ gens_mem wd

theorem hA : m22gA ∈ m22Certificate.originalSubgroup := by
  rw [orig_eq]
  exact gens_mem _ (by simp)

theorem hB : m22gB ∈ m22Certificate.originalSubgroup := by
  rw [orig_eq]
  exact gens_mem _ (by simp)

theorem forall₂_words {ws : List (List ℤ)} {OG : List ℕ} (hl : OG.length = ws.length)
    (h : allN ws.length (fun i => bAnd(abOK (ws.getD i []), Nat.beq (abWordK 22 5 (mask 5)
      (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) (ws.getD i [])) (OG.getD i 0))) =
        true) :
    List.Forall₂ (PRep 22 5) OG (ws.map (evalCodes [m22gA, m22gB])) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
  have hi : i < ws.length := by simpa using h2
  have e1 : OG.get ⟨i, h1⟩ = OG.getD i 0 := by
    rw [List.getD_eq_getElem _ _ h1]
    rfl
  have e2 : (ws.map (evalCodes [m22gA, m22gB])).get ⟨i, h2⟩ =
      evalCodes [m22gA, m22gB] (ws.getD i []) := by
    rw [List.getD_eq_getElem _ _ hi]
    simp
  rw [e1, e2]
  exact prep_word (allN_spec h i hi)

theorem mem_of_forall₂ {OG' : List ℕ} {og : List (Equiv.Perm (Fin 22))}
    (h : List.Forall₂ (PRep 22 5) OG' og) {g : Equiv.Perm (Fin 22)} (hg : g ∈ og) :
    ∃ i < OG'.length, PRep 22 5 (OG'.getD i 0) g := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hl := h.length_eq
  refine ⟨i, hl ▸ hi, ?_⟩
  rw [List.getD_eq_getElem _ _ (hl ▸ hi)]
  exact (List.forall₂_iff_get.1 h).2 i _ hi

theorem sq_of {U : Nat} {u : Equiv.Perm (Fin 22)} (pU : PRep 22 5 U u)
    (h : Nat.beq (pcomp 22 5 (mask 5) U U) (pidn 22 5) = true) : u * u = 1 := by
  rw [beq_eq_decide (by norm_num) (prep_pcomp hn pU pU) (prep_pidn (by norm_num) (by norm_num))
    (PF.pcomp_shr _ _ hn (by norm_num)) (PF.pidn_shr (by norm_num) (by norm_num))] at h
  exact of_decide_eq_true h

theorem hog_of {U : Nat} {u : Equiv.Perm (Fin 22)} (pU : PRep 22 5 U u) {ws : List (List ℤ)}
    {OG' : List ℕ} (hW : List.Forall₂ (PRep 22 5) OG' (ws.map (evalCodes [m22gA, m22gB])))
    {e k : ℕ} (hk : OG'.length = k)
    (h : allN k (fun i => bAnd(Nat.beq (pcomp 22 5 (mask 5) U (OG'.getD i 0))
      (pcomp 22 5 (mask 5) (OG'.getD i 0) U),
      Nat.beq (powK 22 5 (mask 5) (pidn 22 5) (OG'.getD i 0) e) (pidn 22 5))) = true) :
    ∀ g ∈ ws.map (evalCodes [m22gA, m22gB]), u * g = g * u ∧ g ^ e = 1 := by
  intro g hg
  obtain ⟨i, hi, pg⟩ := mem_of_forall₂ hW hg
  have h2 := and_of_bAnd (allN_spec h i (hk ▸ hi))
  exact ⟨mul_eq_of szOK' pU pg pg pU h2.1, pow_eq_one_of szOK' pg h2.2⟩

theorem cand_of {u : Equiv.Perm (Fin 22)} {rows : List (ℕ × ℕ × List ℕ)}
    (hc : ∀ x ∈ m22Certificate.originalSubgroup, (u * x) * (u * x) = 1 →
      ∃ X, PRep 22 5 X x ∧ rowsPK 22 5 rows X = true)
    (r : Row) {OG' : List ℕ} (hr : (r.prime, r.prime ^ r.pexp, OG') ∈ rows) :
    ∀ x ∈ m22Certificate.originalSubgroup, (u * x) * (u * x) = 1 → orderOf x = r.prime →
      ∃ X, PRep 22 5 X x ∧ witPK 22 5 OG' (r.prime ^ r.pexp) X = true := by
  intro x hx hsq hxo
  obtain ⟨X, pX, hX⟩ := hc x hx hsq
  exact ⟨X, pX, witPK_of_rowsPK pX hX hr hxo⟩

theorem hord : m22Certificate.orderCertificate = 443520 :=
  (chainK_check (by decide) (by decide) chainQ).2.trans (by decide)

theorem hcovI : ∀ s, (1 : Equiv.Perm (Fin 22))⁻¹ * s ∈ m22Certificate.originalSubgroup →
    orderOf s = 2 → ∃ r ∈ m22InvReps, ∃ c ∈ m22Certificate.originalSubgroup, s = c * r * c⁻¹ := by
  refine (exists_conj_of_repsOK hn m22Certificate valid (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (by norm_num) m22InvReps (fun r hr => ?_) 2000 cover.1).1
  have e : m22InvReps = [m22InvReps.getD 0 1] := rfl
  rw [e, List.mem_singleton] at hr
  subst hr
  have hm : m22InvReps.getD 0 1 = evalCodes [m22gA, m22gB] (m22InvRepWords.getD 0 []) := rfl
  refine ⟨by rw [inv_one, one_mul, hm]; exact word_mem _, ?_⟩
  have h := cover.2.2
  rw [e] at h
  exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 (by simpa using h)

theorem dinv : m22Delta⁻¹ = m22Delta := (eq_inv_of_mul_eq_one_left delta.1).symm

theorem hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
    m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
  have hsift := m22Certificate.sift_eq_true_iff_mem_original valid
  have h1 := conj_mem_of_gens orig_eq ((hsift _).1 delta.2.1) ((hsift _).1 delta.2.2.1)
  intro h hh
  have e : m22Delta⁻¹ * h * m22Delta = m22Delta * h * m22Delta⁻¹ := by rw [dinv]
  rw [e]
  exact h1 h hh

theorem outRep_mem (j : ℕ) (hj : j < 2) :
    m22Delta⁻¹ * m22OutReps.getD j 1 ∈ m22Certificate.originalSubgroup := by
  interval_cases j
  · have e : m22OutReps.getD 0 1 = evalCodes [m22gA, m22gB] (m22OutRepWords.getD 0 []) *
        m22Delta := rfl
    rw [e, ← mul_assoc]
    exact hg₀ _ (word_mem _)
  · have e : m22OutReps.getD 1 1 = evalCodes [m22gA, m22gB] (m22OutRepWords.getD 1 []) *
        m22Delta := rfl
    rw [e, ← mul_assoc]
    exact hg₀ _ (word_mem _)

theorem hcovO : ∀ s, m22Delta⁻¹ * s ∈ m22Certificate.originalSubgroup →
    orderOf s = 2 → ∃ r ∈ m22OutReps, ∃ c ∈ m22Certificate.originalSubgroup, s = c * r * c⁻¹ := by
  refine (exists_conj_of_repsOK hn m22Certificate valid (pairTables_spec hn hA hB) m22Delta
    hg₀ (by norm_num) m22OutReps (fun r hr => ?_) 2000 ocover.1).1
  have e : m22OutReps = [m22OutReps.getD 0 1, m22OutReps.getD 1 1] := rfl
  have h := ocover.2.2
  rw [e] at h
  rw [e] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨outRep_mem 0 (by norm_num),
      (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
        (List.all_eq_true.1 h _ (by simp))⟩
  · exact ⟨outRep_mem 1 (by norm_num),
      (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
        (List.all_eq_true.1 h _ (by simp))⟩

theorem pUI : PRep 22 5 UI (m22InvReps.getD 0 1) := prep_of_imageList (hR.2 0 (by decide))

theorem pUA : PRep 22 5 UA (m22OutReps.getD 0 1) := prep_of_imageList (hRO.2 0 (by decide))

theorem pUB : PRep 22 5 UB (m22OutReps.getD 1 1) := prep_of_imageList (hRO.2 1 (by decide))

theorem candI : ∀ x ∈ m22Certificate.originalSubgroup,
    (m22InvReps.getD 0 1 * x) * (m22InvReps.getD 0 1 * x) = 1 →
      ∃ X, PRep 22 5 X x ∧ rowsPK 22 5 rowsIK X = true := by
  have hu : (1 : Equiv.Perm (Fin 22))⁻¹ * m22InvReps.getD 0 1 ∈ m22Certificate.originalSubgroup := by
    have hm : m22InvReps.getD 0 1 = evalCodes [m22gA, m22gB] (m22InvRepWords.getD 0 []) := rfl
    rw [inv_one, one_mul, hm]
    exact word_mem _
  exact cands_of_classes szOK' pAc pBc clsOK2 ⟨hR.1, fun j hj => prep_of_imageList (hR.2 j hj)⟩
    (by decide) orig_eq hu hcovI (prep_pinvS (by norm_num) pUI).1 (fun j hj => by
      have hj1 : j < 1 := by simpa [M22CK] using hj
      interval_cases j
      exact f3I)

theorem candA : ∀ x ∈ m22Certificate.originalSubgroup,
    (m22OutReps.getD 0 1 * x) * (m22OutReps.getD 0 1 * x) = 1 →
      ∃ X, PRep 22 5 X x ∧ rowsPK 22 5 rowsAK X = true :=
  cands_of_classes szOK' pAc pBc oclsOK ⟨hRO.1, fun j hj => prep_of_imageList (hRO.2 j hj)⟩
    (by decide) orig_eq (outRep_mem 0 (by norm_num)) hcovO (prep_pinvS (by norm_num) pUA).1
    (fun j hj => by
      have hj2 : j < 2 := by simpa [M22OCL] using hj
      interval_cases j
      · exact f3A0
      · exact f3A1)

theorem candB : ∀ x ∈ m22Certificate.originalSubgroup,
    (m22OutReps.getD 1 1 * x) * (m22OutReps.getD 1 1 * x) = 1 →
      ∃ X, PRep 22 5 X x ∧ rowsPK 22 5 rowsBK X = true :=
  cands_of_classes szOK' pAc pBc oclsOK ⟨hRO.1, fun j hj => prep_of_imageList (hRO.2 j hj)⟩
    (by decide) orig_eq (outRep_mem 1 (by norm_num)) hcovO (prep_pinvS (by norm_num) pUB).1
    (fun j hj => by
      have hj2 : j < 2 := by simpa [M22OCL] using hj
      interval_cases j
      · exact f3B0
      · exact f3B1)

theorem innOK : rowsOK 22 m22Certificate [m22gA, m22gB] (m22InvReps.getD 0 1)
    Certificates.Odd87F3.M22.rowsInn = true := by
  unfold rowsOK
  simp only [Certificates.Odd87F3.M22.rowsInn, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  have hu := sq_of pUI uSq.1
  have w3 := forall₂_words (ws := Certificates.Odd87F3.M22.oddWordsInn_3) (OG := OGI3) rfl bOGI3
  have w5 := forall₂_words (ws := Certificates.Odd87F3.M22.oddWordsInn_5) (OG := OGI5) rfl bOGI5
  refine ⟨rowOK_of_cands szOK' _ valid _ hu ⟨3, 2, 3, _⟩ w3 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pUI w3 rfl ogI.1) (cand_of candI ⟨3, 2, 3, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨5, 1, 3, _⟩ w5 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pUI w5 rfl ogI.2) (cand_of candI ⟨5, 1, 3, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨7, 1, 1, []⟩ (OG := []) .nil (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (by simp) (cand_of candI ⟨7, 1, 1, []⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨11, 1, 1, []⟩ (OG := []) .nil (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (by simp) (cand_of candI ⟨11, 1, 1, []⟩ (by decide))⟩

theorem out1OK : rowsOK 22 m22Certificate [m22gA, m22gB] (m22OutReps.getD 0 1)
    Certificates.Odd87F3.M22.rowsOut1 = true := by
  unfold rowsOK
  simp only [Certificates.Odd87F3.M22.rowsOut1, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  have hu := sq_of pUA uSq.2.1
  have w3 := forall₂_words (ws := Certificates.Odd87F3.M22.oddWordsOut1_3) (OG := OGA3) rfl bOGA3
  have w5 := forall₂_words (ws := Certificates.Odd87F3.M22.oddWordsOut1_5) (OG := OGA5) rfl bOGA5
  have w11 := forall₂_words (ws := Certificates.Odd87F3.M22.oddWordsOut1_11) (OG := OGA11) rfl
    bOGA11
  refine ⟨rowOK_of_cands szOK' _ valid _ hu ⟨3, 2, 5, _⟩ w3 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pUA w3 rfl ogA.1) (cand_of candA ⟨3, 2, 5, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨5, 1, 5, _⟩ w5 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pUA w5 rfl ogA.2.1)
    (cand_of candA ⟨5, 1, 5, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨7, 1, 1, []⟩ (OG := []) .nil (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (by simp) (cand_of candA ⟨7, 1, 1, []⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨11, 1, 5, _⟩ w11 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pUA w11 rfl ogA.2.2)
    (cand_of candA ⟨11, 1, 5, _⟩ (by decide))⟩

theorem out2OK : rowsOK 22 m22Certificate [m22gA, m22gB] (m22OutReps.getD 1 1)
    Certificates.Odd87F3.M22.rowsOut2 = true := by
  unfold rowsOK
  simp only [Certificates.Odd87F3.M22.rowsOut2, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  have hu := sq_of pUB uSq.2.2
  have w3 := forall₂_words (ws := Certificates.Odd87F3.M22.oddWordsOut2_3) (OG := OGB3) rfl bOGB3
  refine ⟨rowOK_of_cands szOK' _ valid _ hu ⟨3, 2, 3, _⟩ w3 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pUB w3 rfl ogB) (cand_of candB ⟨3, 2, 3, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨5, 1, 1, []⟩ (OG := []) .nil (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (by simp) (cand_of candB ⟨5, 1, 1, []⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨7, 1, 1, []⟩ (OG := []) .nil (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (by simp) (cand_of candB ⟨7, 1, 1, []⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨11, 1, 1, []⟩ (OG := []) .nil (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (by simp) (cand_of candB ⟨11, 1, 1, []⟩ (by decide))⟩

theorem f3OK : Certificates.Odd87F3.M22.m22F3OK = true := by
  unfold Certificates.Odd87F3.M22.m22F3OK
  rw [innOK, out1OK, out2OK]
  rfl

abbrev a0 : Equiv.Perm (Fin 22) := evalCodes [m22gA, m22gB] Certificates.CF67.M22.wa

abbrev b0 : Equiv.Perm (Fin 22) := evalCodes [m22gA, m22gB] Certificates.CF67.M22.wb

theorem pA0 : PRep 22 5 PA0 a0 := prep_word bA0

theorem pB0 : PRep 22 5 PB0 b0 := prep_word bB0

abbrev hGens : List (Equiv.Perm (Fin 22)) := MathieuC3.m22Words.map (evalCodes [m22gA, m22gB])

theorem chainH : ChainK 22 5 hGens MathieuC3.m22ChainWords (#v[2, 1] : Vector (Fin 22) 2)
    M22CH.S M22CH.SI M22CH.LR M22CH.TR M22CH.TRI 4 M22CH.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M22CH.head, M22CH.hl,
    by norm_num, M22CH.hs⟩
  have hj3 : j < 3 := by simpa [hGens, MathieuC3.m22Words] using hj
  rw [getD_map_eval]
  have h := allN_spec bH j hj3
  exact img_word (and_of_bAnd h).1 (and_of_bAnd h).2

abbrev HQ : RawSchreierDatum 22 :=
  certificate (by decide) hGens MathieuC3.m22ChainWords #v[2, 1] (by decide)

theorem H_le : HQ.originalSubgroup ≤
    m22Certificate.originalSubgroup ⊓ Subgroup.centralizer ({a0} : Set (Equiv.Perm (Fin 22))) := by
  rw [certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ hGens := hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  have hj3 : j < 3 := by simpa [hGens, MathieuC3.m22Words] using hj
  have pg : PRep 22 5 (M22CH.S j) hGens[j] := by
    have := prep_of_imageList (chainH.2.2.2.1 j hj)
    rwa [List.getD_eq_getElem _ _ hj] at this
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 (mul_eq_of szOK' pg pA0 pA0 pg
    (allN_spec hComm j hj3))⟩
  rw [List.getElem_map]
  exact word_mem _

theorem card_H : Nat.card HQ.originalSubgroup = 36 :=
  (card_group chainH (by decide) (by decide)).trans (Nat.eq_of_beq_eq_true hOrd)

theorem card_C : Nat.card ↥(m22Certificate.originalSubgroup ⊓
    Subgroup.centralizer ({a0} : Set (Equiv.Perm (Fin 22)))) = 36 :=
  (card_centralizer_eq chainQ (by decide) (by decide) (by norm_num) pA0).trans
    (Nat.eq_of_beq_eq_true cent)

theorem H_eq : HQ.originalSubgroup =
    m22Certificate.originalSubgroup ⊓ Subgroup.centralizer ({a0} : Set (Equiv.Perm (Fin 22))) :=
  Subgroup.eq_of_le_of_card_ge H_le (by rw [card_H, card_C])

theorem hel : ∀ g ∈ HQ.originalSubgroup, g * b0 = b0 * g → g ^ 9 = 1 := by
  intro g hg hgb
  obtain ⟨j, hj, rfl⟩ := (mem_group_iff chainH (by decide) (by decide) _).1 hg
  have hj' : j < 36 := by
    have := Nat.eq_of_beq_eq_true hOrd
    omega
  have pE := prep_elemK chainH j
  have h := allN_spec elems j hj'
  unfold powCommK at h
  rw [beq_pcomp_iff hn (by norm_num) pE pB0 pB0 pE, decide_eq_true hgb] at h
  exact pow_eq_one_of szOK' pE (by simpa using h)

theorem cf67 : Certificates.CF67.M22.m22CF67OK = true := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := abFacts
  unfold Certificates.CF67.M22.m22CF67OK Certificates.CF67.cf67OK
  exact cf67OKT_of szOK' valid pA0 pB0 (Nat.eq_of_beq_eq_true abShr.1)
    (Nat.eq_of_beq_eq_true abShr.2) f1 f2 f3 f4 f5 (by rw [hord]; norm_num)
    (commAll_pow hn valid H_eq.symm.le hel)

end CertificateChecks.KernelSporSch.M22W

end
