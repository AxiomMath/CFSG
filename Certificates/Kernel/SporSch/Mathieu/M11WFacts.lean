module

public import Certificates.Kernel.SporSch.Mathieu.M11WChecks
public import Certificates.Kernel.SporSch.Mathieu.M11Facts
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

namespace CertificateChecks.KernelSporSch.M11W

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.KS.SporSch.OddWit CFSG.KS.SporSch
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M11OC
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 Certificates.Odd87F3 CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem hn : (11 : ℕ) < 2 ^ 32 := by norm_num

theorem valid : ValidSchreier m11Certificate := chainK_valid chainQ (by decide) (by decide)

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem prep_word {wd : List ℤ} {P : ℕ} (h : bAnd(abOK wd, Nat.beq (abWordK 11 4 (mask 4)
    (pidn 11 4) (M11Q.S 0) (M11Q.SI 0) (M11Q.S 1) (M11Q.SI 1) wd) P) = true) :
    PRep 11 4 P (evalCodes [m11gA, m11gB] wd) :=
  prep_of_imageList (img_word (and_of_bAnd h).1 (and_of_bAnd h).2)

theorem orig_eq : m11Certificate.originalSubgroup =
    Subgroup.closure ({m11gA, m11gB} : Set (Equiv.Perm (Fin 11))) := by
  rw [m11Certificate, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem pAc : PRep 11 4 (packL 4 tA) m11gA := by
  rw [tA_eq]
  exact (prep_packL (by norm_num)).1

theorem pBc : PRep 11 4 (packL 4 tB) m11gB := by
  rw [tB_eq]
  exact (prep_packL (by norm_num)).1

theorem gens_mem : ∀ g ∈ [m11gA, m11gB],
    g ∈ Subgroup.closure ({m11gA, m11gB} : Set (Equiv.Perm (Fin 11))) := by
  intro g hg
  apply Subgroup.subset_closure
  simpa using hg

theorem word_mem (wd : List ℤ) : evalCodes [m11gA, m11gB] wd ∈ m11Certificate.originalSubgroup := by
  rw [orig_eq]
  exact evalCodes_mem _ gens_mem wd

theorem forall₂_words {ws : List (List ℤ)} {OG : List ℕ} (hl : OG.length = ws.length)
    (h : allN ws.length (fun i => bAnd(abOK (ws.getD i []), Nat.beq (abWordK 11 4 (mask 4)
      (pidn 11 4) (M11Q.S 0) (M11Q.SI 0) (M11Q.S 1) (M11Q.SI 1) (ws.getD i [])) (OG.getD i 0))) =
        true) :
    List.Forall₂ (PRep 11 4) OG (ws.map (evalCodes [m11gA, m11gB])) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
  have hi : i < ws.length := by simpa using h2
  have e1 : OG.get ⟨i, h1⟩ = OG.getD i 0 := by
    rw [List.getD_eq_getElem _ _ h1]
    rfl
  have e2 : (ws.map (evalCodes [m11gA, m11gB])).get ⟨i, h2⟩ =
      evalCodes [m11gA, m11gB] (ws.getD i []) := by
    rw [List.getD_eq_getElem _ _ hi]
    simp
  rw [e1, e2]
  exact prep_word (allN_spec h i hi)

theorem elems_of_blocks {f : Nat → Bool} {c nb : Nat} (hc : c ≤ nb * 256)
    (h : ∀ s < nb, allBlk (s * 256) f 256 = true) : ∀ k < c, f k = true := by
  intro k hk
  have hs : k / 256 < nb := by omega
  have := allBlk_spec (h (k / 256) hs) (k % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (k / 256 * 256) (k % 256) = k := by
    change k / 256 * 256 + k % 256 = k
    omega
  rwa [e] at this

abbrev u : Equiv.Perm (Fin 11) := m11InvReps.getD 0 1

theorem pU : PRep 11 4 U u := by
  rw [Nat.eq_of_beq_eq_true repU]
  exact prep_of_imageList imgRep

theorem pUi : PRep 11 4 (pinvS 11 4 (mask 4) U) u⁻¹ := (prep_pinvS (by norm_num) pU).1

theorem huK : u ∈ m11Certificate.originalSubgroup := by
  have e : u = evalCodes [m11gA, m11gB] (m11InvRepWords.getD 0 []) := rfl
  rw [e]
  exact word_mem _

theorem uSq' : u * u = 1 := by
  have h := uSq
  rw [beq_eq_decide (by norm_num) (prep_pcomp hn pU pU) (prep_pidn (by norm_num) (by norm_num))
    (PF.pcomp_shr _ _ hn (by norm_num)) (PF.pidn_shr (by norm_num) (by norm_num))] at h
  exact of_decide_eq_true h

theorem mem_of_forall₂ {OG' : List ℕ} {og : List (Equiv.Perm (Fin 11))}
    (h : List.Forall₂ (PRep 11 4) OG' og) {g : Equiv.Perm (Fin 11)} (hg : g ∈ og) :
    ∃ i < OG'.length, PRep 11 4 (OG'.getD i 0) g := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hl := h.length_eq
  refine ⟨i, hl ▸ hi, ?_⟩
  rw [List.getD_eq_getElem _ _ (hl ▸ hi)]
  exact (List.forall₂_iff_get.1 h).2 i _ hi

theorem clsCK : ClsOK 11 4 tA tB 2 400 M11WCK := by
  intro j hj
  have hj1 : j < 1 := by simpa [M11WCK] using hj
  interval_cases j
  exact ⟨M11WCK.h0, elems_of_blocks (by decide) M11WCK.hb0, fun i hi => absurd hi (by omega)⟩

theorem hcov : ∀ s, (1 : Equiv.Perm (Fin 11))⁻¹ * s ∈ m11Certificate.originalSubgroup →
    orderOf s = 2 → ∃ r ∈ m11InvReps, ∃ c ∈ m11Certificate.originalSubgroup, s = c * r * c⁻¹ := by
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [orig_eq]
    exact gens_mem _ (by simp)
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [orig_eq]
    exact gens_mem _ (by simp)
  refine (exists_conj_of_repsOK hn m11Certificate valid (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (by norm_num) m11InvReps (fun r hr => ?_) 400 cover.1).1
  have e : m11InvReps = [u] := rfl
  rw [e, List.mem_singleton] at hr
  subst hr
  refine ⟨by simpa using huK, ?_⟩
  have h := cover.2.2
  rw [e] at h
  exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 (by simpa using h)

theorem cands : ∀ x ∈ m11Certificate.originalSubgroup, (u * x) * (u * x) = 1 →
    ∃ X, PRep 11 4 X x ∧ rowsPK 11 4 rowsK X = true :=
  cands_of_classes szOK' pAc pBc clsCK
    ⟨rfl, fun j hj => by
      have hj1 : j < 1 := by simpa [M11WCK] using hj
      interval_cases j
      exact pU⟩ (by decide) orig_eq (g₀ := 1) (by simpa using huK) hcov pUi
    (fun j hj => by
      have hj1 : j < 1 := by simpa [M11WCK] using hj
      interval_cases j
      exact f3)

theorem cand (r : Row) {OG' : List ℕ} (hr : (r.prime, r.prime ^ r.pexp, OG') ∈ rowsK) :
    ∀ x ∈ m11Certificate.originalSubgroup, (u * x) * (u * x) = 1 → orderOf x = r.prime →
      ∃ X, PRep 11 4 X x ∧ witPK 11 4 OG' (r.prime ^ r.pexp) X = true := by
  intro x hx hsq hxo
  obtain ⟨X, pX, hX⟩ := cands x hx hsq
  exact ⟨X, pX, witPK_of_rowsPK pX hX hr hxo⟩

theorem hW : List.Forall₂ (PRep 11 4) OG
    (Certificates.Odd87F3.M11.oddWords.map (evalCodes [m11gA, m11gB])) :=
  forall₂_words (ws := Certificates.Odd87F3.M11.oddWords) (OG := OG) rfl bOG

theorem hog : ∀ g ∈ Certificates.Odd87F3.M11.oddWords.map (evalCodes [m11gA, m11gB]),
    u * g = g * u ∧ g ^ 495 = 1 := by
  intro g hg
  obtain ⟨i, hi, pg⟩ := mem_of_forall₂ hW hg
  exact ⟨mul_eq_of szOK' pU pg pg pU (allN_spec ogComm i hi),
    pow_eq_one_of szOK' pg (allN_spec ogPow i hi)⟩

theorem hord : m11Certificate.orderCertificate = 7920 :=
  (chainK_check (by decide) (by decide) chainQ).2.trans (by decide)

theorem f3OK : Certificates.Odd87F3.M11.m11F3OK = true := by
  unfold Certificates.Odd87F3.M11.m11F3OK rowsOK
  simp only [Certificates.Odd87F3.M11.rows, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  refine ⟨rowOK_of_cands szOK' _ valid _ uSq' ⟨3, 2, 495, _⟩ hW (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) hog (cand ⟨3, 2, 495, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ uSq' ⟨5, 1, 495, _⟩ hW (by norm_num) (by norm_num)
    (by rw [hord]; norm_num) hog (cand ⟨5, 1, 495, _⟩ (by decide)),
    rowOK_of_cands szOK' _ valid _ uSq' ⟨11, 1, 495, []⟩ (OG := []) .nil (by norm_num)
    (by norm_num) (by rw [hord]; norm_num) (by simp) (cand ⟨11, 1, 495, []⟩ (by decide))⟩

abbrev a0 : Equiv.Perm (Fin 11) := evalCodes [m11gA, m11gB] Certificates.CF67.M11.wa

abbrev b0 : Equiv.Perm (Fin 11) := evalCodes [m11gA, m11gB] Certificates.CF67.M11.wb

theorem pA0 : PRep 11 4 A0 a0 := prep_word bA0

theorem pB0 : PRep 11 4 B0 b0 := prep_word bB0

abbrev hGens : List (Equiv.Perm (Fin 11)) := MathieuC3.m11Words.map (evalCodes [m11gA, m11gB])

theorem chainH : ChainK 11 4 hGens MathieuC3.m11ChainWords (#v[2, 0] : Vector (Fin 11) 2)
    M11CH.S M11CH.SI M11CH.LR M11CH.TR M11CH.TRI 4 M11CH.BP 1 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M11CH.head, M11CH.hl,
    by norm_num, M11CH.hs⟩
  have hj3 : j < 3 := by simpa [hGens, MathieuC3.m11Words] using hj
  rw [getD_map_eval]
  have h := allN_spec bH j hj3
  exact img_word (and_of_bAnd h).1 (and_of_bAnd h).2

abbrev HQ : RawSchreierDatum 11 :=
  certificate (by decide) hGens MathieuC3.m11ChainWords #v[2, 0] (by decide)

theorem H_le : HQ.originalSubgroup ≤
    m11Certificate.originalSubgroup ⊓ Subgroup.centralizer ({a0} : Set (Equiv.Perm (Fin 11))) := by
  rw [certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ hGens := hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  have hj3 : j < 3 := by simpa [hGens, MathieuC3.m11Words] using hj
  have pg : PRep 11 4 (M11CH.S j) hGens[j] := by
    have := prep_of_imageList (chainH.2.2.2.1 j hj)
    rwa [List.getD_eq_getElem _ _ hj] at this
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 (mul_eq_of szOK' pg pA0 pA0 pg
    (allN_spec hComm j hj3))⟩
  rw [List.getElem_map]
  exact word_mem _

theorem card_H : Nat.card HQ.originalSubgroup = 18 :=
  (card_group chainH (by decide) (by decide)).trans (Nat.eq_of_beq_eq_true hOrd)

theorem card_C : Nat.card ↥(m11Certificate.originalSubgroup ⊓
    Subgroup.centralizer ({a0} : Set (Equiv.Perm (Fin 11)))) = 18 :=
  (card_centralizer_eq chainQ (by decide) (by decide) (by norm_num) pA0).trans
    (Nat.eq_of_beq_eq_true cent)

theorem H_eq : HQ.originalSubgroup =
    m11Certificate.originalSubgroup ⊓ Subgroup.centralizer ({a0} : Set (Equiv.Perm (Fin 11))) :=
  Subgroup.eq_of_le_of_card_ge H_le (by rw [card_H, card_C])

theorem hel : ∀ g ∈ HQ.originalSubgroup, g * b0 = b0 * g → g ^ 9 = 1 := by
  intro g hg hgb
  obtain ⟨j, hj, rfl⟩ := (mem_group_iff chainH (by decide) (by decide) _).1 hg
  have hj' : j < 18 := by
    have := Nat.eq_of_beq_eq_true hOrd
    omega
  have pE := prep_elemK chainH j
  have h := allN_spec elems j hj'
  unfold powCommK at h
  rw [beq_pcomp_iff hn (by norm_num) pE pB0 pB0 pE, decide_eq_true hgb] at h
  exact pow_eq_one_of szOK' pE (by simpa using h)

theorem cf67 : Certificates.CF67.M11.m11CF67OK = true := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := abFacts
  unfold Certificates.CF67.M11.m11CF67OK Certificates.CF67.cf67OK
  exact cf67OKT_of szOK' valid pA0 pB0 (Nat.eq_of_beq_eq_true abShr.1)
    (Nat.eq_of_beq_eq_true abShr.2) f1 f2 f3 f4 f5 (by rw [hord]; norm_num)
    (commAll_pow hn valid H_eq.symm.le hel)

end CertificateChecks.KernelSporSch.M11W

end
