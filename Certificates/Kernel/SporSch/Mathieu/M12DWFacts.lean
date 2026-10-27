module

public import Certificates.Kernel.SporSch.Mathieu.M12DWChecks
public import Certificates.Kernel.SporSch.Mathieu.M12MFacts
public import CFSG.Certificates.Kernel.SporSch.MathieuOddGlue
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Abs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12DW

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.OddWit CFSG.KS.SporSch
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M12MOC
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 Certificates.Odd87F3

theorem hn : (24 : ℕ) < 2 ^ 32 := by norm_num

theorem valid : ValidSchreier m12D := chainK_valid chainQ (by decide) (by decide)

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem prep_word {wd : List ℤ} {P : ℕ} (h : bAnd(abOK wd, Nat.beq (abWordK 24 5 (mask 5)
    (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1) wd) P) = true) :
    PRep 24 5 P (evalCodes [m12A1, m12B1] wd) :=
  prep_of_imageList (img_word (and_of_bAnd h).1 (and_of_bAnd h).2)

theorem orig_eq : m12D.originalSubgroup =
    Subgroup.closure ({m12A1, m12B1} : Set (Equiv.Perm (Fin 24))) := by
  rw [m12D, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem pAc : PRep 24 5 (packL 5 tA) m12A1 := by
  rw [tA_eq]
  exact (prep_packL (by norm_num)).1

theorem pBc : PRep 24 5 (packL 5 tB) m12B1 := by
  rw [tB_eq]
  exact (prep_packL (by norm_num)).1

theorem gens_mem : ∀ g ∈ [m12A1, m12B1],
    g ∈ Subgroup.closure ({m12A1, m12B1} : Set (Equiv.Perm (Fin 24))) := by
  intro g hg
  apply Subgroup.subset_closure
  simpa using hg

theorem word_mem (wd : List ℤ) : evalCodes [m12A1, m12B1] wd ∈ m12D.originalSubgroup := by
  rw [orig_eq]
  exact evalCodes_mem _ gens_mem wd

theorem hA : m12A1 ∈ m12D.originalSubgroup := by
  rw [orig_eq]
  exact gens_mem _ (by simp)

theorem hB : m12B1 ∈ m12D.originalSubgroup := by
  rw [orig_eq]
  exact gens_mem _ (by simp)

theorem forall₂_words {ws : List (List ℤ)} {OG : List ℕ} (hl : OG.length = ws.length)
    (h : allN ws.length (fun i => bAnd(abOK (ws.getD i []), Nat.beq (abWordK 24 5 (mask 5)
      (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1) (ws.getD i []))
        (OG.getD i 0))) = true) :
    List.Forall₂ (PRep 24 5) OG (ws.map (evalCodes [m12A1, m12B1])) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
  have hi : i < ws.length := by simpa using h2
  have e1 : OG.get ⟨i, h1⟩ = OG.getD i 0 := by
    rw [List.getD_eq_getElem _ _ h1]
    rfl
  have e2 : (ws.map (evalCodes [m12A1, m12B1])).get ⟨i, h2⟩ =
      evalCodes [m12A1, m12B1] (ws.getD i []) := by
    rw [List.getD_eq_getElem _ _ hi]
    simp
  rw [e1, e2]
  exact prep_word (allN_spec h i hi)

theorem mem_of_forall₂ {OG' : List ℕ} {og : List (Equiv.Perm (Fin 24))}
    (h : List.Forall₂ (PRep 24 5) OG' og) {g : Equiv.Perm (Fin 24)} (hg : g ∈ og) :
    ∃ i < OG'.length, PRep 24 5 (OG'.getD i 0) g := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hl := h.length_eq
  refine ⟨i, hl ▸ hi, ?_⟩
  rw [List.getD_eq_getElem _ _ (hl ▸ hi)]
  exact (List.forall₂_iff_get.1 h).2 i _ hi

theorem sq_of {U : Nat} {u : Equiv.Perm (Fin 24)} (pU : PRep 24 5 U u)
    (h : Nat.beq (pcomp 24 5 (mask 5) U U) (pidn 24 5) = true) : u * u = 1 := by
  rw [beq_eq_decide (by norm_num) (prep_pcomp hn pU pU) (prep_pidn (by norm_num) (by norm_num))
    (PF.pcomp_shr _ _ hn (by norm_num)) (PF.pidn_shr (by norm_num) (by norm_num))] at h
  exact of_decide_eq_true h

theorem hog_of {U : Nat} {u : Equiv.Perm (Fin 24)} (pU : PRep 24 5 U u) {ws : List (List ℤ)}
    {OG' : List ℕ} (hW : List.Forall₂ (PRep 24 5) OG' (ws.map (evalCodes [m12A1, m12B1])))
    {e k : ℕ} (hk : OG'.length = k)
    (h : allN k (fun i => bAnd(Nat.beq (pcomp 24 5 (mask 5) U (OG'.getD i 0))
      (pcomp 24 5 (mask 5) (OG'.getD i 0) U),
      Nat.beq (powK 24 5 (mask 5) (pidn 24 5) (OG'.getD i 0) e) (pidn 24 5))) = true) :
    ∀ g ∈ ws.map (evalCodes [m12A1, m12B1]), u * g = g * u ∧ g ^ e = 1 := by
  intro g hg
  obtain ⟨i, hi, pg⟩ := mem_of_forall₂ hW hg
  have h2 := and_of_bAnd (allN_spec h i (hk ▸ hi))
  exact ⟨mul_eq_of szOK' pU pg pg pU h2.1, pow_eq_one_of szOK' pg h2.2⟩

theorem cand_of {u : Equiv.Perm (Fin 24)} {rows : List (ℕ × ℕ × List ℕ)}
    (hc : ∀ x ∈ m12D.originalSubgroup, (u * x) * (u * x) = 1 →
      ∃ X, PRep 24 5 X x ∧ rowsPK 24 5 rows X = true)
    (r : Row) {OG' : List ℕ} (hr : (r.prime, r.prime ^ r.pexp, OG') ∈ rows) :
    ∀ x ∈ m12D.originalSubgroup, (u * x) * (u * x) = 1 → orderOf x = r.prime →
      ∃ X, PRep 24 5 X x ∧ witPK 24 5 OG' (r.prime ^ r.pexp) X = true := by
  intro x hx hsq hxo
  obtain ⟨X, pX, hX⟩ := hc x hx hsq
  exact ⟨X, pX, witPK_of_rowsPK pX hX hr hxo⟩

theorem clsI : ClsOK 24 5 tA tB 2 1000 M12ICL := by
  intro j hj
  have hj2 : j < 2 := by simpa [M12ICL] using hj
  interval_cases j
  · exact ⟨M12ICL.h0, elems_of_blocks (by decide) M12ICL.hb0, fun i hi => absurd hi (by omega)⟩
  · refine ⟨M12ICL.h1, elems_of_blocks (by decide) M12ICL.hb1, fun i hi => ?_⟩
    have hi0 : i = 0 := by omega
    subst hi0
    exact M12ICL.n1_0

theorem hRI : Certificates.Odd87F3.M12.innerReps.length = M12ICL.length ∧ ∀ j < M12ICL.length,
    imageList (Certificates.Odd87F3.M12.innerReps.getD j 1) =
      (unpack 24 5 (M12ICL.getD j clsD0).R).toList := by
  refine ⟨rfl, fun j hj => ?_⟩
  have hj2 : j < 2 := by simpa [M12ICL] using hj
  interval_cases j
  · have e1 : Certificates.Odd87F3.M12.innerReps.getD 0 1 =
        evalCodes [m12A1, m12B1] Certificates.Odd87F3.M12.repWordInn1 := rfl
    have e2 : (M12ICL.getD 0 clsD0).R = U1 := rfl
    rw [e1, e2]
    exact imageList_of_prep (prep_word bRep.1)
  · have e1 : Certificates.Odd87F3.M12.innerReps.getD 1 1 =
        evalCodes [m12A1, m12B1] Certificates.Odd87F3.M12.repWordInn2 := by
      simp only [Certificates.Odd87F3.M12.innerReps, List.getD_cons_succ, List.getD_cons_zero]
    have e2 : (M12ICL.getD 1 clsD0).R = U2 := rfl
    rw [e1, e2]
    exact imageList_of_prep (prep_word bRep.2)

theorem imgOne : imageList (1 : Equiv.Perm (Fin 24)) = (unpack 24 5 One).toList := by
  decide

theorem cosetIX : (cosetOrderTables m12D 1 2).length = (M12IX.CS.map List.sum).sum :=
  chainK_cosetCount2 (by decide) (by decide) chainQ imgOne cOne (by norm_num) (by norm_num) M12IX.hc

theorem coverI : repsOK 24 (pairTables m12A1 m12B1) (pairTables m12A1⁻¹ m12B1⁻¹)
      (cosetOrderTables m12D 1 2) (Certificates.Odd87F3.M12.innerReps.map toTable) 1000 = true ∧
    (Certificates.Odd87F3.M12.innerReps.map toTable).all (ordTest 24 2) = true := by
  obtain ⟨h1, -, h3⟩ := chainK_reps3 tA_eq tB_eq szOK' clsI hRI (by norm_num)
    (X := cosetOrderTables m12D 1 2) (by rw [cosetIX]; decide)
  exact ⟨h1, h3⟩

theorem coverOK_true : coverOK 24 m12D m12A1 m12B1 1 Certificates.Odd87F3.M12.innerReps 1000 =
    true := by
  unfold coverOK
  rw [coverI.1, Bool.true_and]
  simpa [List.all_map] using coverI.2

theorem inner_mem (j : ℕ) (hj : j < 2) :
    Certificates.Odd87F3.M12.innerReps.getD j 1 ∈ m12D.originalSubgroup := by
  interval_cases j
  · exact word_mem _
  · exact word_mem _

theorem hcovI : ∀ s, (1 : Equiv.Perm (Fin 24))⁻¹ * s ∈ m12D.originalSubgroup →
    orderOf s = 2 → ∃ r ∈ Certificates.Odd87F3.M12.innerReps,
      ∃ c ∈ m12D.originalSubgroup, s = c * r * c⁻¹ := by
  refine (exists_conj_of_repsOK hn m12D valid (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (by norm_num) _ (fun r hr => ?_) 1000 coverI.1).1
  have e : Certificates.Odd87F3.M12.innerReps = [Certificates.Odd87F3.M12.innerReps.getD 0 1,
      Certificates.Odd87F3.M12.innerReps.getD 1 1] := rfl
  have h := coverI.2
  rw [e] at h
  rw [e] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨by rw [inv_one, one_mul]; exact inner_mem 0 (by norm_num),
      (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
        (List.all_eq_true.1 h _ (by simp))⟩
  · exact ⟨by rw [inv_one, one_mul]; exact inner_mem 1 (by norm_num),
      (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
        (List.all_eq_true.1 h _ (by simp))⟩

theorem sinv : m12Sigma⁻¹ = m12Sigma := (eq_inv_of_mul_eq_one_left sigma.1).symm

theorem hg₀ : ∀ h ∈ m12D.originalSubgroup, m12Sigma⁻¹ * h * m12Sigma ∈ m12D.originalSubgroup := by
  have hsift := m12D.sift_eq_true_iff_mem_original valid
  have h1 := conj_mem_of_gens orig_eq ((hsift _).1 sigma.2.1) ((hsift _).1 sigma.2.2.1)
  intro h hh
  have e : m12Sigma⁻¹ * h * m12Sigma = m12Sigma * h * m12Sigma⁻¹ := by rw [sinv]
  rw [e]
  exact h1 h hh

theorem hs₀ : m12Sigma⁻¹ * m12Sigma ∈ m12D.originalSubgroup := by
  rw [inv_mul_cancel]
  exact m12D.originalSubgroup.one_mem

theorem hcovS : ∀ s, m12Sigma⁻¹ * s ∈ m12D.originalSubgroup →
    orderOf s = 2 → ∃ r ∈ [m12Sigma], ∃ c ∈ m12D.originalSubgroup, s = c * r * c⁻¹ := by
  refine (exists_conj_of_repsOK hn m12D valid (pairTables_spec hn hA hB) m12Sigma
    hg₀ (by norm_num) _ (fun r hr => ?_) 1000 cover.1).1
  rw [List.mem_singleton] at hr
  subst hr
  exact ⟨hs₀, (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 cover.2.2⟩

theorem pU1 : PRep 24 5 U1 (Certificates.Odd87F3.M12.innerReps.getD 0 1) :=
  prep_of_imageList (hRI.2 0 (by decide))

theorem pU2 : PRep 24 5 U2 (Certificates.Odd87F3.M12.innerReps.getD 1 1) :=
  prep_of_imageList (hRI.2 1 (by decide))

theorem pUS : PRep 24 5 M12S m12Sigma := prep_of_imageList imgS

theorem hRS : [m12Sigma].length = M12SCL.length ∧ ∀ j < M12SCL.length,
    PRep 24 5 (M12SCL.getD j clsD0).R ([m12Sigma].getD j 1) :=
  ⟨hR.1, fun j hj => prep_of_imageList (hR.2 j hj)⟩

theorem cand1 : ∀ x ∈ m12D.originalSubgroup,
    (Certificates.Odd87F3.M12.innerReps.getD 0 1 * x) *
      (Certificates.Odd87F3.M12.innerReps.getD 0 1 * x) = 1 →
      ∃ X, PRep 24 5 X x ∧ rowsPK 24 5 rows1K X = true :=
  cands_of_classes szOK' pAc pBc clsI ⟨hRI.1, fun j hj => prep_of_imageList (hRI.2 j hj)⟩
    (by decide) orig_eq (by rw [inv_one, one_mul]; exact inner_mem 0 (by norm_num)) hcovI
    (prep_pinvS (by norm_num) pU1).1 (fun j hj => by
      have hj2 : j < 2 := by simpa [M12ICL] using hj
      interval_cases j
      · exact f310
      · exact f311)

theorem cand2 : ∀ x ∈ m12D.originalSubgroup,
    (Certificates.Odd87F3.M12.innerReps.getD 1 1 * x) *
      (Certificates.Odd87F3.M12.innerReps.getD 1 1 * x) = 1 →
      ∃ X, PRep 24 5 X x ∧ rowsPK 24 5 rows2K X = true :=
  cands_of_classes szOK' pAc pBc clsI ⟨hRI.1, fun j hj => prep_of_imageList (hRI.2 j hj)⟩
    (by decide) orig_eq (by rw [inv_one, one_mul]; exact inner_mem 1 (by norm_num)) hcovI
    (prep_pinvS (by norm_num) pU2).1 (fun j hj => by
      have hj2 : j < 2 := by simpa [M12ICL] using hj
      interval_cases j
      · exact f320
      · exact f321)

theorem candS : ∀ x ∈ m12D.originalSubgroup, (m12Sigma * x) * (m12Sigma * x) = 1 →
    ∃ X, PRep 24 5 X x ∧ rowsPK 24 5 rowsSK X = true :=
  cands_of_classes szOK' pAc pBc clsOK' hRS (by decide) orig_eq hs₀ hcovS
    (prep_pinvS (by norm_num) pUS).1 (fun j hj => by
      have hj1 : j < 1 := by simpa [M12SCL] using hj
      interval_cases j
      exact f3S)

theorem hord : m12D.orderCertificate = 95040 := model.2

theorem rows1OK : rowsOK 24 m12D [m12A1, m12B1]
    (evalCodes [m12A1, m12B1] Certificates.Odd87F3.M12.repWordInn1)
    Certificates.Odd87F3.M12.rowsInn1 = true := by
  unfold rowsOK
  simp only [Certificates.Odd87F3.M12.rowsInn1, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  have hu := sq_of pU1 uSq.1
  have w3 := forall₂_words (ws := Certificates.Odd87F3.M12.oddWordsInn1_3) (OG := OG13) rfl bOG13
  have w5 := forall₂_words (ws := Certificates.Odd87F3.M12.oddWordsInn1_5) (OG := OG15) rfl bOG15
  exact ⟨rowOK_of_cands szOK' _ valid _ hu ⟨3, 3, 3, _⟩ w3 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pU1 w3 rfl og1.1) (cand_of cand1 ⟨3, 3, 3, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨5, 1, 3, _⟩ w5 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pU1 w5 rfl og1.2) (cand_of cand1 ⟨5, 1, 3, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨11, 1, 1, []⟩ (OG := []) .nil (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (by simp) (cand_of cand1 ⟨11, 1, 1, []⟩ (by decide))⟩

theorem rows2OK : rowsOK 24 m12D [m12A1, m12B1]
    (evalCodes [m12A1, m12B1] Certificates.Odd87F3.M12.repWordInn2)
    Certificates.Odd87F3.M12.rowsInn2 = true := by
  unfold rowsOK
  simp only [Certificates.Odd87F3.M12.rowsInn2, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  have hu := sq_of pU2 uSq.2.1
  have w3 := forall₂_words (ws := Certificates.Odd87F3.M12.oddWordsInn2_3) (OG := OG23) rfl bOG23
  have w5 := forall₂_words (ws := Certificates.Odd87F3.M12.oddWordsInn2_5) (OG := OG25) rfl bOG25
  exact ⟨rowOK_of_cands szOK' _ valid _ hu ⟨3, 3, 5, _⟩ w3 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pU2 w3 rfl og2.1) (cand_of cand2 ⟨3, 3, 5, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨5, 1, 3, _⟩ w5 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pU2 w5 rfl og2.2) (cand_of cand2 ⟨5, 1, 3, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨11, 1, 1, []⟩ (OG := []) .nil (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (by simp) (cand_of cand2 ⟨11, 1, 1, []⟩ (by decide))⟩

theorem rowsSOK : rowsOK 24 m12D [m12A1, m12B1] m12Sigma Certificates.Odd87F3.M12.rowsSig =
    true := by
  unfold rowsOK
  simp only [Certificates.Odd87F3.M12.rowsSig, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  have hu := sq_of pUS uSq.2.2
  have w3 := forall₂_words (ws := Certificates.Odd87F3.M12.oddWordsSig_3) (OG := OGS3) rfl bOGS3
  have w5 := forall₂_words (ws := Certificates.Odd87F3.M12.oddWordsSig_5) (OG := OGS5) rfl bOGS5
  have w11 := forall₂_words (ws := Certificates.Odd87F3.M12.oddWordsSig_11) (OG := OGS11) rfl
    bOGS11
  exact ⟨rowOK_of_cands szOK' _ valid _ hu ⟨3, 3, 5, _⟩ w3 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pUS w3 rfl ogS.1) (cand_of candS ⟨3, 3, 5, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨5, 1, 5, _⟩ w5 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pUS w5 rfl ogS.2.1)
    (cand_of candS ⟨5, 1, 5, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ hu ⟨11, 1, 3, _⟩ w11 (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) (hog_of pUS w11 rfl ogS.2.2)
    (cand_of candS ⟨11, 1, 3, _⟩ (by decide))⟩

theorem f3OK : Certificates.Odd87F3.M12.m12F3OK = true := by
  unfold Certificates.Odd87F3.M12.m12F3OK
  rw [coverOK_true, rows1OK, rows2OK, rowsSOK]
  rfl

end CertificateChecks.KernelSporSch.M12DW

end
