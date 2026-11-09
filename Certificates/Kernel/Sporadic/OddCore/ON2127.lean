module

public import Certificates.Kernel.Sporadic.OddCore.ON2127C
public import Certificates.Kernel.Sporadic.OddCore.ON2127Q
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Sporadic.OddCore.ON2123
public import Certificates.Kernel.Sporadic.ON5.Final
public import CFSG.Certificates.Kernel.Spor.DecSLProved
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.ONOddCore.QuotOuterCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PEnumLSound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2127

open CFSG.ONSchreier.Native hiding posArr
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.PSL3Four.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.KS.DecSL
open CFSG.ComponentClassification.PSL3Four
open CertificateChecks.KernelSpor.ON2127C

@[expose] noncomputable def DC : LocalCert := decodeCert (natsSL LocAutT.chars)

theorem localCert_eq : localCert = DC := by
  rw [localCert, LocAutT.eq, natsOf_ofList_proved ON2123.digits]
  rfl

theorem records_len : DC.records.length = 12 := by
  decide +kernel

@[expose] noncomputable def posK (n w k : Nat) (G : Nat → Nat) (wd : List Nat) : Nat :=
  wd.foldr (fun l acc => CFSG.KC.Enum.pcomp n w (mask w)
    (if l - 1 < k then G (l - 1) else pidn n w) acc) (pidn n w)

theorem getD_eq {gs : Array (Array Nat)} {i : Nat} {d : Array Nat} :
    gs.getD i d = if i < gs.size then gs[i]! else d := by
  by_cases h : i < gs.size
  · simp only [h, ↓reduceIte]
    rw [getElem!_pos gs i h]
    simp [Array.getD, h]
  · simp [Array.getD, h]

theorem posArr_unpack {n w k : Nat} {G : Nat → Nat} {gs : Array (Array Nat)}
    (hid : idK n w (mask w) = true) (hcI : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hs : gs.size = k)
    (hg : ∀ j < k, gs[j]! = unpack n w (G j) ∧ canonK n w (mask w) (n * w) (G j) = true) :
    ∀ wd : List Nat, posArr n gs wd = unpack n w (posK n w k G wd) ∧
      canonK n w (mask w) (n * w) (posK n w k G wd) = true := by
  intro wd
  induction wd with
  | nil =>
    refine ⟨?_, hcI⟩
    change idA n = unpack n w (pidn n w)
    rw [idK_sound hid]
  | cons l wd ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hl : gs.getD (l - 1) (pid n) = unpack n w (if l - 1 < k then G (l - 1) else pidn n w) ∧
        canonK n w (mask w) (n * w) (if l - 1 < k then G (l - 1) else pidn n w) = true := by
      rw [getD_eq, hs]
      by_cases h : l - 1 < k
      · simp only [h, ↓reduceIte]
        exact hg _ h
      · simp only [h, ↓reduceIte]
        refine ⟨?_, hcI⟩
        change idA n = unpack n w (pidn n w)
        rw [idK_sound hid]
    have e1 : posArr n gs (l :: wd) = pcomp n (gs.getD (l - 1) (pid n)) (posArr n gs wd) := rfl
    have e2 : posK n w k G (l :: wd) = CFSG.KC.Enum.pcomp n w (mask w)
        (if l - 1 < k then G (l - 1) else pidn n w) (posK n w k G wd) := rfl
    rw [e1, e2, hl.1, ih1]
    exact ⟨compA_unpack hl.2 ih2, canonK_pcomp hl.2 ih2⟩

@[expose] def decF4 : DecidableEq F4 := fun a b => decidable_of_iff (a.code = b.code)
  ⟨fun h => by cases a; cases b; cases h; rfl, fun h => h ▸ rfl⟩

theorem decF4_eq : (instDecidableEqF4 : DecidableEq F4) = decF4 := Subsingleton.elim _ _

@[expose] def tripleIdxX (I : DecidableEq F4) (t : Triple) : ℕ :=
  @List.idxOf _ (@instBEqOfDecidableEq _ (@instDecidableEqProd _ _ _ (@instDecidableEqProd _ _ _ I)))
    t elemTriples + 1

@[expose] def tripleWordX (I : DecidableEq F4) (t : Triple) : List ℕ :=
  @ite _ (t.2.2 = 1 ∨ t.2.2 = F4.ω) (@instDecidableOr _ _ (I _ _) (I _ _)) [tripleIdxX I t]
    [tripleIdxX I (t.1, t.2.1, 1), tripleIdxX I (t.1, t.2.1, F4.ω)]

@[expose] def sigWordX (I : DecidableEq F4) (d f g m : ℕ) : List ℕ :=
  tripleWordX I (stepT d f g (elemTriples.getD m (0, 1, 1)))

theorem sig_rfl (d f g m : ℕ) : sigWord d f g m = sigWordX instDecidableEqF4 d f g m := rfl

theorem sig_eq (d f g m : ℕ) : sigWord d f g m = sigWordX decF4 d f g m := by
  rw [sig_rfl, decF4_eq]

theorem szOK7 : szOK 120 7 = true := by quickRfl
theorem idk : idK 120 7 (mask 7) = true := by quickRfl
theorem cI : canonK 120 7 (mask 7) (120 * 7) (pidn 120 7) = true := by quickRfl

theorem bQG : allN 2 (fun j => bindListK 120 7 (QP j) (DC.quotGens.getD j #[]).toList) = true := by
  quickRfl
theorem bQC : bindListK 120 7 (QP 2) Data.quotientConjugator.toList = true := by quickRfl
theorem bM : allN 2 (fun j => bindListK 120 7 (QP (3 + j)) Data.M120Chain.generators[j]!.toList) =
    true := by
  quickRfl
theorem bPS : allN 12 (fun m => bindListK 120 7 (QP (5 + m)) Data.PSL120Chain.generators[m]!.toList) =
    true := by quickRfl
theorem bRI : allN 12 (fun k => allN 2 (fun j =>
    bindListK 120 7 (RI (2 * k + j)) ((DC.records.getD k default).images.getD j #[]).toList)) =
    true := by
  quickRfl

theorem eq_of_bindListK {n w P : Nat} {A : Array Nat} (h : bindListK n w P A.toList = true) :
    A = unpack n w P := by
  rw [← toArray_eq_of_bindListK h, Array.toArray_toList]

theorem cQP : allN 17 (fun j => canonK 120 7 (mask 7) (120 * 7) (QP j)) = true := by quickRfl
theorem cRI : allN 24 (fun j => canonK 120 7 (mask 7) (120 * 7) (RI j)) = true := by quickRfl
theorem cQI : canonK 120 7 (mask 7) (120 * 7) (pinvS 120 7 (mask 7) (QP 2)) = true := by quickRfl
theorem pQ : permOK 120 7 (mask 7) (120 * 7) (QP 2) (pinvS 120 7 (mask 7) (QP 2)) = true := by
  quickRfl

theorem kA : allN 2 (fun j => Nat.beq (QP j) (CFSG.KC.Enum.pcomp 120 7 (mask 7) (QP 2)
    (CFSG.KC.Enum.pcomp 120 7 (mask 7) (QP (3 + j)) (pinvS 120 7 (mask 7) (QP 2))))) = true := by
  quickRfl

theorem kB : allN 12 (fun m => Nat.beq (posK 120 7 2 QP xWords[m]!) (QP (5 + m))) = true := by
  quickRfl

theorem kD : allN 12 (fun k => allN 12 (fun m =>
    Nat.beq (posK 120 7 2 (fun j => RI (2 * k + j)) xWords[m]!)
      (posK 120 7 12 (fun j => QP (5 + j)) (sigWordX decF4 (DC.records.getD k default).diag
        (DC.records.getD k default).field (DC.records.getD k default).graph m)))) = true := by
  quickRfl

theorem kF : allN 12 (fun k => allN 2 (fun j => bAnd(Nat.blt (List.getD qIdx (2 * k + j) 0) ON5M.cnt,
    Nat.beq (ON5M.T (List.getD qIdx (2 * k + j) 0))
      (CFSG.KC.Enum.pcomp 120 7 (mask 7) (pinvS 120 7 (mask 7) (QP 2))
        (CFSG.KC.Enum.pcomp 120 7 (mask 7) (RI (2 * k + j)) (QP 2)))))) = true := by
  quickRfl

theorem xLetters : (xWords.all fun w => w.all fun l => 1 ≤ l && l ≤ 2) = true := by
  unfold xWords
  rw [List.all_toArray]
  decide +kernel

theorem qg_get : ∀ j < 2, qgArr j = unpack 120 7 (QP j) ∧
    canonK 120 7 (mask 7) (120 * 7) (QP j) = true := fun j hj => by
  rw [qgArr, localCert_eq]
  exact ⟨eq_of_bindListK (allN_spec bQG j hj), allN_spec cQP j (by omega)⟩

theorem qc_get : Data.quotientConjugator = unpack 120 7 (QP 2) := eq_of_bindListK bQC

theorem cQ : canonK 120 7 (mask 7) (120 * 7) (QP 2) = true := allN_spec cQP 2 (by omega)

theorem qci_get :
    pinvCand 120 Data.quotientConjugator = unpack 120 7 (pinvS 120 7 (mask 7) (QP 2)) := by
  rw [qc_get]
  exact invCand_unpack pQ

theorem ps_size : Data.PSL120Chain.generators.size = 12 := by decide +kernel

theorem ps_get : ∀ j < 12, Data.PSL120Chain.generators[j]! = unpack 120 7 (QP (5 + j)) ∧
    canonK 120 7 (mask 7) (120 * 7) (QP (5 + j)) = true := fun j hj =>
  ⟨eq_of_bindListK (allN_spec bPS j hj), allN_spec cQP (5 + j) (by omega)⟩

theorem ri_get : ∀ k < 12, ∀ j < 2, qiArr (DC.records.getD k default) j =
    unpack 120 7 (RI (2 * k + j)) ∧ canonK 120 7 (mask 7) (120 * 7) (RI (2 * k + j)) = true :=
  fun k hk j hj => ⟨eq_of_bindListK (allN_spec (allN_spec bRI k hk) j hj),
    allN_spec cRI (2 * k + j) (by omega)⟩

theorem pair_get {a b : Array Nat} {G : Nat → Nat}
    (ha : a = unpack 120 7 (G 0) ∧ canonK 120 7 (mask 7) (120 * 7) (G 0) = true)
    (hb : b = unpack 120 7 (G 1) ∧ canonK 120 7 (mask 7) (120 * 7) (G 1) = true) :
    ∀ j < 2, (#[a, b])[j]! = unpack 120 7 (G j) ∧ canonK 120 7 (mask 7) (120 * 7) (G j) = true := by
  intro j hj
  interval_cases j
  · exact ha
  · exact hb

theorem quot_conj : ∀ j < 2, peq 120 (qgArr j) (pcomp 120 Data.quotientConjugator
    (pcomp 120 Data.M120Chain.generators[j]! (pinvCand 120 Data.quotientConjugator))) = true := by
  intro j hj
  have cm := allN_spec cQP (3 + j) (by omega)
  rw [(qg_get j hj).1, eq_of_bindListK (allN_spec bM j hj), qci_get, qc_get]
  change eqA 120 _ (compA 120 _ (compA 120 _ _)) = true
  rw [compA_unpack cm cQI, compA_unpack cQ (canonK_pcomp cm cQI),
    eqA_unpack (qg_get j hj).2 (canonK_pcomp cQ (canonK_pcomp cm cQI))]
  exact allN_spec kA j hj

theorem quot_words : ∀ m < 12, peq 120 (posArr 120 #[qgArr 0, qgArr 1] xWords[m]!)
    Data.PSL120Chain.generators[m]! = true := by
  intro m hm
  obtain ⟨h1, h2⟩ := posArr_unpack (k := 2) (G := QP) idk cI rfl (pair_get (qg_get 0 (by omega))
    (qg_get 1 (by omega))) xWords[m]!
  rw [h1, (ps_get m hm).1]
  change eqA 120 _ _ = true
  rw [eqA_unpack h2 (ps_get m hm).2]
  exact allN_spec kB m hm

theorem rec_words : ∀ k < 12, ∀ m < 12,
    peq 120 (posArr 120 #[qiArr (DC.records.getD k default) 0,
      qiArr (DC.records.getD k default) 1] xWords[m]!)
      (posArr 120 Data.PSL120Chain.generators (sigWord (DC.records.getD k default).diag
        (DC.records.getD k default).field (DC.records.getD k default).graph m)) = true := by
  intro k hk m hm
  rw [sig_eq]
  obtain ⟨h1, h2⟩ := posArr_unpack (k := 2) (G := fun j => RI (2 * k + j)) idk cI rfl
    (pair_get (ri_get k hk 0 (by omega)) (ri_get k hk 1 (by omega))) xWords[m]!
  obtain ⟨h3, h4⟩ := posArr_unpack (k := 12) (G := fun j => QP (5 + j)) idk cI ps_size ps_get
    (sigWordX decF4 (DC.records.getD k default).diag (DC.records.getD k default).field
      (DC.records.getD k default).graph m)
  rw [h1, h3]
  change eqA 120 _ _ = true
  rw [eqA_unpack h2 h4]
  exact allN_spec (allN_spec kD k hk) m hm

theorem m120_eq : m120Enum = penumRec 120 7 ON5M.cnt ON5M.T ON5M.PL :=
  CertificateChecks.KernelSpor.ON5K.m120_sound.1

theorem found_rec : ∀ k < 12, ∀ j < 2, found (indexOf m120Enum.tabs) m120Enum.tabs
    (pcomp 120 (pinvCand 120 Data.quotientConjugator)
      (pcomp 120 (qiArr (DC.records.getD k default) j) Data.quotientConjugator)) = true := by
  intro k hk j hj
  obtain ⟨hr, cr⟩ := ri_get k hk j hj
  obtain ⟨hlt, he⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec kF k hk) j hj)
  rw [hr, qci_get, qc_get]
  change found _ _ (compA 120 _ (compA 120 _ _)) = true
  rw [compA_unpack cr cQ, compA_unpack cQI (canonK_pcomp cr cQ), m120_eq]
  exact penum_found_sound (fun _ hi => CertificateChecks.KernelSpor.ON5K.m_pt hi)
    (Nat.blt_eq ▸ hlt) (Nat.eq_of_beq_eq_true he)

@[expose] noncomputable def dblPK (P A B : Nat) : Bool :=
  allN 120 (fun i => bAnd(Nat.beq (pg 8 (mask 8) P i) (pg 7 (mask 7) A i),
    Nat.beq (pg 8 (mask 8) P (i + 120)) (pg 7 (mask 7) B i + 120)))

theorem pairUpk_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem pairUpk_size (n w P : Nat) : (unpack n w P).size = n := by
  rw [unpack, Array.size_ofFn]

theorem dblArr_get_lo {n i : Nat} {a b : Array Nat} (ha : a.size = n) (hi : i < n) :
    (dbl n a b)[i]! = a[i]! := by
  unfold dbl
  rw [getElem!_pos (a ++ b.map (· + n)) i (by rw [Array.size_append]; omega),
    Array.getElem_append_left (by omega), getElem!_pos a i (by omega)]

theorem dblArr_get_hi {n i : Nat} {a b : Array Nat} (ha : a.size = n) (hb : b.size = n)
    (hi : n ≤ i) (hi2 : i < n + n) : (dbl n a b)[i]! = b[i - n]! + n := by
  unfold dbl
  rw [getElem!_pos (a ++ b.map (· + n)) i (by rw [Array.size_append, Array.size_map]; omega),
    Array.getElem_append_right (by omega), Array.getElem_map, getElem!_pos b (i - n) (by omega)]
  simp only [ha]

theorem dbl_eq_of {U X Y : Array Nat} {n : Nat} (hU : U.size = n + n) (hX : X.size = n)
    (hY : Y.size = n) (h : ∀ i < n, U[i]! = X[i]! ∧ U[i + n]! = Y[i]! + n) : U = dbl n X Y := by
  apply Array.ext
  · rw [hU, dbl, Array.size_append, Array.size_map, hX, hY]
  · intro i hi1 hi2
    rw [← getElem!_pos U i hi1, ← getElem!_pos (dbl n X Y) i hi2]
    rcases Nat.lt_or_ge i n with hl | hl
    · rw [dblArr_get_lo hX hl]
      exact (h i hl).1
    · rw [dblArr_get_hi hX hY hl (by omega)]
      have e := (h (i - n) (by omega)).2
      rw [Nat.sub_add_cancel hl] at e
      exact e

theorem dbl_of_dblPK {P A B : Nat} (h : dblPK P A B = true) :
    unpack 240 8 P = dbl 120 (unpack 120 7 A) (unpack 120 7 B) := by
  unfold dblPK at h
  have he := allN_spec h
  refine dbl_eq_of (pairUpk_size 240 8 P) (pairUpk_size 120 7 A) (pairUpk_size 120 7 B)
    fun i hi => ?_
  obtain ⟨b1, b2⟩ := (bAnd_iff _ _).1 (he i hi)
  exact ⟨(pairUpk_get (by omega)).trans ((Nat.eq_of_beq_eq_true b1).trans (pairUpk_get hi).symm),
    (pairUpk_get (by omega)).trans ((Nat.eq_of_beq_eq_true b2).trans
      (congrArg (· + 120) (pairUpk_get hi)).symm)⟩

theorem arrExt6 {U V : Array (Array Nat)} (hU : U.size = 6) (hV : V.size = 6)
    (h : ∀ i < 6, U[i]! = V[i]!) : U = V := by
  apply Array.ext
  · rw [hU, hV]
  · intro i h1 h2
    rw [← getElem!_pos U i h1, ← getElem!_pos V i h2]
    exact h i (by omega)

theorem idk8 : idK 240 8 (mask 8) = true := by quickRfl
theorem cI8 : canonK 240 8 (mask 8) (240 * 8) (pidn 240 8) = true := by quickRfl

@[expose] noncomputable def pairLinkK (k : Nat) (PS : Nat → Nat) : Bool :=
  bAnd(allN 2 (fun i => bAnd(dblPK (PS i) (QP i) (RI (2 * k + i)),
      canonK 240 8 (mask 8) (240 * 8) (PS i))),
    allN 4 (fun j => Nat.beq (posK 240 8 2 PS pairPosWords[j]!) (PS (2 + j))))

theorem strongs_link {k : Nat} (hk : k < 12) {PS : Nat → Nat} (h : pairLinkK k PS = true) :
    pairStrongs (DC.records.getD k default) = pairSU PS := by
  unfold pairLinkK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hg : ∀ j < 2, (pairGens (DC.records.getD k default))[j]! = unpack 240 8 (PS j) ∧
      canonK 240 8 (mask 8) (240 * 8) (PS j) = true := by
    intro j hj
    obtain ⟨hd, hc⟩ := (bAnd_iff _ _).1 (allN_spec h1 j hj)
    refine ⟨?_, hc⟩
    rw [CFSG.Sporadic.ONOddCore.pairGens_get _ hj, (qg_get j hj).1, (ri_get k hk j hj).1]
    exact (dbl_of_dblPK hd).symm
  have hw := posArr_unpack (k := 2) idk8 cI8 (pairGens_size _) hg
  refine arrExt6 (pairStrongs_size _) (pairSU_size PS) fun i hi6 => ?_
  refine Eq.trans ?_ (pairSU_get PS hi6).symm
  rcases Nat.lt_or_ge i 2 with hi | hi
  · exact (pairStrongs_get _ i (by rw [pairGens_size]; exact hi)).trans (hg i hi).1
  · obtain ⟨j, rfl⟩ : ∃ j, i = 2 + j := ⟨i - 2, by omega⟩
    have hj : j < 4 := by omega
    exact (pairStrongs_word _ hj).trans (((hw _).1).trans
      (congrArg (unpack 240 8) (Nat.eq_of_beq_eq_true (allN_spec h2 j hj))))

theorem lk0 : pairLinkK 0 C0.S = true := by quickRfl
theorem lk1 : pairLinkK 1 C1.S = true := by quickRfl
theorem lk2 : pairLinkK 2 C2.S = true := by quickRfl
theorem lk3 : pairLinkK 3 C3.S = true := by quickRfl
theorem lk4 : pairLinkK 4 C4.S = true := by quickRfl
theorem lk5 : pairLinkK 5 C5.S = true := by quickRfl
theorem lk6 : pairLinkK 6 C6.S = true := by quickRfl
theorem lk7 : pairLinkK 7 C7.S = true := by quickRfl
theorem lk8 : pairLinkK 8 C8.S = true := by quickRfl
theorem lk9 : pairLinkK 9 C9.S = true := by quickRfl
theorem lk10 : pairLinkK 10 C10.S = true := by quickRfl
theorem lk11 : pairLinkK 11 C11.S = true := by quickRfl

theorem allBelowN_of {n : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) : allBelowN n p = true := by
  unfold allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨i, hi⟩ -
  exact h i hi

theorem rec_ok {k : Nat} (hk : k < 12) {PS : Nat → Nat} (hc : PairChain (pairSU PS))
    (hl : pairLinkK k PS = true) :
    recordCheck (indexOf m120Enum.tabs) (DC.records.getD k default) = true := by
  have e1 : pairChainBase = baseP := rfl
  have e2 : pairDerWords = DP := rfl
  unfold recordCheck
  rw [strongs_link hk hl, e1, e2]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨allBelowN_of fun j hj => found_rec k hk j hj, hc.1⟩, hc.2⟩,
    allBelowN_of fun m hm => rec_words k hk m hm⟩

theorem rec_ok_all : ∀ k < 12,
    recordCheck (indexOf m120Enum.tabs) (DC.records.getD k default) = true := by
  intro k hk
  interval_cases k
  · exact rec_ok (by norm_num) chain0 lk0
  · exact rec_ok (by norm_num) chain1 lk1
  · exact rec_ok (by norm_num) chain2 lk2
  · exact rec_ok (by norm_num) chain3 lk3
  · exact rec_ok (by norm_num) chain4 lk4
  · exact rec_ok (by norm_num) chain5 lk5
  · exact rec_ok (by norm_num) chain6 lk6
  · exact rec_ok (by norm_num) chain7 lk7
  · exact rec_ok (by norm_num) chain8 lk8
  · exact rec_ok (by norm_num) chain9 lk9
  · exact rec_ok (by norm_num) chain10 lk10
  · exact rec_ok (by norm_num) chain11 lk11

theorem facts2127 : quotCheck (indexOf m120Enum.tabs) = true := by
  unfold quotCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨allBelowN_of quot_conj, allBelowN_of quot_words⟩, xLetters⟩, ?_⟩
  rw [List.all_eq_true]
  intro r hr
  rw [localCert_eq] at hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  have hk' : k < 12 := by
    rw [records_len] at hk
    exact hk
  have h := rec_ok_all k hk'
  rwa [List.getD_eq_getElem _ _ hk] at h

end CertificateChecks.KernelSpor.ON2127

end
