module

public import Certificates.Kernel.Sporadic.OddCore.ON2125G
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Sporadic.OddCore.ON2120F

public section

set_option linter.unusedSectionVars false

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2125

open CFSG.ONSchreier.Native hiding posArr
open CFSG.ONSchreier CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore
open CFSG.KS.TW CFSG.KS.PW CertificateChecks.KernelSpor.ON3 CFSG.KS
open CFSG.KC.Enum hiding pcomp
open CertificateChecks.KernelSpor.ON2119 CertificateChecks.KernelSpor.ON2120

@[expose] noncomputable def P (w : List Nat) (x : Nat) : Nat := wordF 3 mG w x

@[expose] noncomputable def PI (w : List Nat) (x : Nat) : Nat := wordF 3 mGI w.reverse x

@[expose] noncomputable def bF (e : LiftEntry) (j x : Nat) : Nat := P (e.words.getD j []) x

@[expose] noncomputable def bFI (e : LiftEntry) (j x : Nat) : Nat := PI (e.words.getD j []) x

theorem ne_of_not_beq {a b : Nat} (h : (!Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem bltT {i k : Nat} (h : i < k) : Nat.blt i k = true := by
  rw [Nat.blt_eq]
  exact h

theorem bltF {i k : Nat} (h : ¬ i < k) : Nat.blt i k = false := by
  cases hc : Nat.blt i k with
  | false => rfl
  | true => rw [Nat.blt_eq] at hc; exact absurd hc h

@[expose] noncomputable def deltaF (e e' : LiftEntry) (nw cw vw : List Nat) (ε : Bool) (i x : Nat) :
    Nat :=
  nIf(Nat.blt i 3, PI nw (bF e i (P nw x)),
    CT (P cw ((fun y => Bool.rec (motive := fun _ => Nat) (bF e' (i - 3) y)
      (wordF 3 (bF e') vw (bF e' (i - 3) (wordF 3 (bFI e') vw.reverse y))) ε)
      (PI cw (CIT x)))))

@[expose] noncomputable def auxP (W : NonextWords) : Bool :=
  lettersOK 3 W.tWord && b3 (P W.tWord) (DT 0) && lettersOK 3 W.vWord &&
    b3 (P W.vWord) (fun p => CIT (ZT (CT p))) &&
    (List.range 4).all fun i => lettersOK 3 (W.dWords.getD i []) &&
      lettersOK 3 (W.dcWords.getD i []) && b3 (P (W.dWords.getD i [])) (DT i) &&
      b3 (P (W.dcWords.getD i [])) (fun p => CIT (DT i (CT p)))

@[expose] noncomputable def exclP (L : List LiftEntry) (W : NonextWords) (rel : List Nat)
    (x : ExclRec) : Bool :=
  let e := L.getD x.index default
  let e' := L.getD x.second default
  lettersOK 3 x.normWord && lettersOK 3 x.conjWord && decide (x.second < L.length) &&
    e.words.length == 3 && e'.words.length == 3 &&
    b3 (fun p => P x.normWord (DT 0 (PI x.normWord p))) (wordF 3 (bF e) W.tWord) &&
    (List.range 4).all (fun i =>
      b3 (fun p => P x.conjWord (wordF 3 (bF e') (W.dcWords.getD i []) (PI x.conjWord p)))
        (fun p => CIT (PI x.normWord (wordF 3 (bF e) (W.dWords.getD i []) (P x.normWord (CT p)))))) &&
    [false, true].all fun ε =>
      !Nat.beq (wordF 6 (deltaF e e' x.normWord x.conjWord W.vWord ε) rel 0) 0

@[expose] noncomputable def innerP (L : List LiftEntry) (y : InnerRec) : Bool :=
  lettersOK 3 y.conjWord && (L.getD y.index default).words.length == 3 &&
    (List.range 3).all fun i =>
      b3 (fun p => P y.conjWord (mG i (PI y.conjWord p))) (bF (L.getD y.index default) i)

@[expose] noncomputable def nonextP (L : List LiftEntry) (C : NonextCert) (W : NonextWords) : Bool :=
  auxP W && lettersOK 6 C.relationWord && b3 (wordF 6 ambF C.relationWord) (fun p => p) &&
    C.excluded.all (exclP L W C.relationWord) && C.inner.all (innerP L)

section B


theorem hgood : ∀ i < (wordArrs Data.MWords).size, Good (wordArrs Data.MWords)[i]! (mG i) :=
  fun i hi => good_hA (by rwa [mwords_size] at hi)

theorem good_P (w : List Nat) : Good (posArr nPts (wordArrs Data.MWords) w) (P w) := by
  have h := good_posArr hgood w
  rwa [mwords_size] at h

theorem good_PI (w : List Nat) :
    Good (pinvCand nPts (posArr nPts (wordArrs Data.MWords) w)) (PI w) ∧
      pisInv nPts (posArr nPts (wordArrs Data.MWords) w)
        (pinvCand nPts (posArr nPts (wordArrs Data.MWords) w)) = true := by
  have h := good_posInv hgood hA_inv w
  rwa [mwords_size] at h

theorem b_inv (e : LiftEntry) : InvMaps 3 (bF e) (bFI e) := by
  intro i _ y hy
  have hm : InvMaps 3 mG mGI := by rw [← mwords_size]; exact hA_inv
  obtain ⟨h1, h2⟩ := wordF_inv hm (e.words.getD i []) y hy
  exact ⟨h1, wordF_lt hm _ hy, h2⟩

theorem good_b {e : LiftEntry} (_he : e.words.length = 3) :
    ∀ i < (liftArrs (wordArrs Data.MWords) e).size,
      Good (liftArrs (wordArrs Data.MWords) e)[i]! (bF e i) := by
  intro i hi
  have hi' : i < e.words.length := by simpa [liftArrs] using hi
  exact good_liftArrs hi'

theorem lift_size {e : LiftEntry} (he : e.words.length = 3) :
    (liftArrs (wordArrs Data.MWords) e).size = 3 := by
  simp [liftArrs, he]

theorem peq_b3 {t u : Array Nat} {F G : Nat → Nat} (ht : Good t F) (hu : Good u G)
    (h : b3 F G = true) : peq nPts t u = true := by
  unfold b3 at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Nat.beq_eq] at h
  exact peq_good ht hu h.1 h.2.1 h.2.2

theorem auxOK_of {W : NonextWords} (h : auxP W = true) :
    auxOK (wordArrs Data.MWords) W = true := by
  simp only [auxP, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [auxOK, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨h1, peq_b3 (good_P _) good_t h2⟩, h3⟩, peq_b3 (good_P _) good_vArr h4⟩, fun i hi => ?_⟩
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h5 i hi
  exact ⟨⟨⟨a1, a2⟩, peq_b3 (good_P _) (good_d hi) a3⟩, peq_b3 (good_P _) (good_dConj hi) a4⟩

theorem good_delta {e e' : LiftEntry} (he : e.words.length = 3) (he' : e'.words.length = 3)
    (nw cw vw : List Nat) (ε : Bool) :
    ∀ i < (deltaImgs (liftArrs (wordArrs Data.MWords) e) (liftArrs (wordArrs Data.MWords) e')
        (posArr nPts (wordArrs Data.MWords) nw) (pinvCand nPts (posArr nPts (wordArrs Data.MWords) nw))
        (posArr nPts (wordArrs Data.MWords) cw) (pinvCand nPts (posArr nPts (wordArrs Data.MWords) cw))
        (posArr nPts (liftArrs (wordArrs Data.MWords) e') vw)
        (pinvCand nPts (posArr nPts (liftArrs (wordArrs Data.MWords) e') vw)) ε).size,
      Good (deltaImgs (liftArrs (wordArrs Data.MWords) e) (liftArrs (wordArrs Data.MWords) e')
        (posArr nPts (wordArrs Data.MWords) nw) (pinvCand nPts (posArr nPts (wordArrs Data.MWords) nw))
        (posArr nPts (wordArrs Data.MWords) cw) (pinvCand nPts (posArr nPts (wordArrs Data.MWords) cw))
        (posArr nPts (liftArrs (wordArrs Data.MWords) e') vw)
        (pinvCand nPts (posArr nPts (liftArrs (wordArrs Data.MWords) e') vw)) ε)[i]!
        (deltaF e e' nw cw vw ε i) := by
  intro i hi
  have hs : ∀ (a b : Array (Array Nat)) (f g : Array Nat → Array Nat),
      (a.map f ++ b.map g).size = a.size + b.size := by simp
  unfold deltaImgs at hi ⊢
  rw [hs, lift_size he, lift_size he'] at hi
  have hbv := good_posArr (good_b he') vw
  have hbvi := good_posInv (good_b he') (by rw [lift_size he']; exact b_inv e') vw
  rw [lift_size he'] at hbv hbvi
  rw [getElem!_pos _ i (by simp [lift_size he, lift_size he']; omega)]
  by_cases h3 : i < 3
  · rw [Array.getElem_append_left (by simp [lift_size he]; exact h3)]
    simp only [Array.getElem_map]
    have e1 : deltaF e e' nw cw vw ε i = fun x => PI nw (bF e i (P nw x)) := by
      funext x
      unfold deltaF
      rw [bltT h3]
    rw [e1, ← getElem!_pos _ i (by rw [lift_size he]; exact h3)]
    exact good_conjArr (good_PI nw).1 (good_P nw) (good_b he i (by rw [lift_size he]; exact h3))
  · rw [Array.getElem_append_right (by simp [lift_size he]; omega)]
    simp only [Array.getElem_map, Array.size_map, lift_size he]
    have hb := good_b he' (i - 3) (by rw [lift_size he']; omega)
    rw [← getElem!_pos _ (i - 3) (by rw [lift_size he']; omega)]
    cases ε with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have e1 : deltaF e e' nw cw vw false i = fun x => CT (P cw (bF e' (i - 3) (PI cw (CIT x)))) := by
        funext x
        unfold deltaF
        rw [bltF h3]
      rw [e1]
      exact good_cConj (good_conjArr (good_P cw) (good_PI cw).1 hb)
    | true =>
      simp only [↓reduceIte]
      have e1 : deltaF e e' nw cw vw true i = fun x => CT (P cw (wordF 3 (bF e') vw
          (bF e' (i - 3) (wordF 3 (bFI e') vw.reverse (PI cw (CIT x)))))) := by
        funext x
        unfold deltaF
        rw [bltF h3]
      rw [e1]
      exact good_cConj (good_conjArr (good_P cw) (good_PI cw).1
        (good_conjArr hbv hbvi.1 hb))

theorem exclOK_of {L : List LiftEntry} {W : NonextWords} {rel : List Nat} {x : ExclRec}
    (h : exclP L W rel x = true) : exclOK (wordArrs Data.MWords) L W rel x = true := by
  simp only [exclP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, he⟩, he'⟩, ht⟩, hd⟩, hδ⟩ := h
  have hbv := good_posInv (good_b he') (by rw [lift_size he']; exact b_inv _) W.vWord
  simp only [exclOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, (good_PI _).2⟩, (good_PI _).2⟩, hbv.2⟩, ?_⟩, ?_⟩, ?_⟩
  · have hb := good_posArr (good_b he) W.tWord
    rw [lift_size he] at hb
    exact peq_b3 (good_conjArr (good_P _) (good_PI _).1 good_t) hb ht
  · intro i hi
    have hb := good_posArr (good_b he) (W.dWords.getD i [])
    have hb' := good_posArr (good_b he') (W.dcWords.getD i [])
    rw [lift_size he] at hb
    rw [lift_size he'] at hb'
    exact peq_b3 (good_conjArr (good_P _) (good_PI _).1 hb')
      (good_conjArr good_ci good_c (good_conjArr (good_PI _).1 (good_P _) hb)) (hd i hi)
  · intro ε hε
    have hg := good_posArr (good_delta he he' x.normWord x.conjWord W.vWord ε) rel
    have hsz : (deltaImgs (liftArrs (wordArrs Data.MWords) (L.getD x.index default))
        (liftArrs (wordArrs Data.MWords) (L.getD x.second default))
        (posArr nPts (wordArrs Data.MWords) x.normWord)
        (pinvCand nPts (posArr nPts (wordArrs Data.MWords) x.normWord))
        (posArr nPts (wordArrs Data.MWords) x.conjWord)
        (pinvCand nPts (posArr nPts (wordArrs Data.MWords) x.conjWord))
        (posArr nPts (liftArrs (wordArrs Data.MWords) (L.getD x.second default)) W.vWord)
        (pinvCand nPts (posArr nPts (liftArrs (wordArrs Data.MWords) (L.getD x.second default))
          W.vWord)) ε).size = 6 := by
      simp only [deltaImgs, Array.size_append, Array.size_map, lift_size he, lift_size he']
    rw [hsz] at hg
    rw [(hg.2.2 0 (by norm_num)).1]
    have := ne_of_not_beq (hδ ε hε)
    simpa [bne] using this

theorem innerOK_of {L : List LiftEntry} {y : InnerRec} (h : innerP L y = true) :
    innerOK (wordArrs Data.MWords) L y = true := by
  simp only [innerP, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, he⟩, h3⟩ := h
  simp only [innerOK, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨h1, (good_PI _).2⟩, fun i hi => ?_⟩
  exact peq_b3 (good_conjArr (good_P _) (good_PI _).1 (good_hA hi))
    (good_b he i (by rw [lift_size he]; exact hi)) (h3 i hi)

theorem nonextOK_of {L : List LiftEntry} {C : NonextCert} {W : NonextWords}
    (h : nonextP L C W = true) : nonextOK (wordArrs Data.MWords) L C W = true := by
  simp only [nonextP, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [nonextOK, Bool.and_eq_true, List.all_eq_true]
  have hg := good_posArr good_amb C.relationWord
  rw [amb_size] at hg
  exact ⟨⟨⟨⟨auxOK_of h1, h2⟩, peq_b3 hg good_pid h3⟩, fun x hx => exclOK_of (h4 x hx)⟩,
    fun y hy => innerOK_of (h5 y hy)⟩

end B

theorem flatLifts_eq : flatLifts = CLit.records.flatMap QuotRecord.lifts := by
  rw [flatLifts, localCert_eq]

theorem nonext_k : nonextP (CLit.records.flatMap QuotRecord.lifts) nonextCert nonextWords = true := by
  quickRfl

theorem facts2125 :
    nonextOK (wordArrs Data.MWords) flatLifts nonextCert nonextWords = true := by
  rw [flatLifts_eq]
  exact nonextOK_of nonext_k

end CertificateChecks.KernelSpor.ON2125

end
