module

public import Certificates.Kernel.Sporadic.OddCore.ON2127E0
public import Certificates.Kernel.Sporadic.OddCore.ON2127E1
public import Certificates.Kernel.Sporadic.OddCore.ON2127E2
public import Certificates.Kernel.Sporadic.OddCore.ON2127E3
public import Certificates.Kernel.Sporadic.OddCore.ON2127E4
public import Certificates.Kernel.Sporadic.OddCore.ON2127E5
public import Certificates.Kernel.Sporadic.OddCore.ON2127Q
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Sporadic.OddCore.ON2123
public import Certificates.Kernel.Sporadic.ON5.Final
public import CFSG.Certificates.Kernel.Spor.DecSLProved
public import CFSG.Certificates.Kernel.BfsPinUnpack
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

theorem bQG : allN 2 (fun j => bindArrK (DC.quotGens.getD j #[]) 120 7 (QP j)) = true := by
  quickRfl
theorem bQC : bindArrK Data.quotientConjugator 120 7 (QP 2) = true := by quickRfl
theorem bM : allN 2 (fun j => bindArrK Data.M120Chain.generators[j]! 120 7 (QP (3 + j))) =
    true := by
  quickRfl
theorem bPS : allN 12 (fun m => bindArrK Data.PSL120Chain.generators[m]! 120 7 (QP (5 + m))) =
    true := by quickRfl
theorem bRI : allN 12 (fun k => allN 2 (fun j =>
    bindArrK ((DC.records.getD k default).images.getD j #[]) 120 7 (RI (2 * k + j)))) = true := by
  quickRfl

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
  exact ⟨unpack_eq_of_bindArrK (allN_spec bQG j hj), allN_spec cQP j (by omega)⟩

theorem qc_get : Data.quotientConjugator = unpack 120 7 (QP 2) := unpack_eq_of_bindArrK bQC

theorem cQ : canonK 120 7 (mask 7) (120 * 7) (QP 2) = true := allN_spec cQP 2 (by omega)

theorem qci_get :
    pinvCand 120 Data.quotientConjugator = unpack 120 7 (pinvS 120 7 (mask 7) (QP 2)) := by
  rw [qc_get]
  exact invCand_unpack pQ

theorem ps_size : Data.PSL120Chain.generators.size = 12 := by decide +kernel

theorem ps_get : ∀ j < 12, Data.PSL120Chain.generators[j]! = unpack 120 7 (QP (5 + j)) ∧
    canonK 120 7 (mask 7) (120 * 7) (QP (5 + j)) = true := fun j hj =>
  ⟨unpack_eq_of_bindArrK (allN_spec bPS j hj), allN_spec cQP (5 + j) (by omega)⟩

theorem ri_get : ∀ k < 12, ∀ j < 2, qiArr (DC.records.getD k default) j =
    unpack 120 7 (RI (2 * k + j)) ∧ canonK 120 7 (mask 7) (120 * 7) (RI (2 * k + j)) = true :=
  fun k hk j hj => ⟨unpack_eq_of_bindArrK (allN_spec (allN_spec bRI k hk) j hj),
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
  rw [(qg_get j hj).1, unpack_eq_of_bindArrK (allN_spec bM j hj), qci_get, qc_get]
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

theorem szOK8 : szOK 240 8 = true := by quickRfl

theorem root_eq : pairRoot = idTab 240 := by
  apply Array.ext
  · simp [pairRoot, dblBase, idTab]
  · intro i _ _
    simp only [pairRoot, dblBase, idTab, Array.getElem_ofFn, Array.getElem_append,
      Array.size_range, Array.getElem_map, Array.getElem_range]
    split <;> omega

@[expose] noncomputable def pgD (r : QuotRecord) : Array Tab :=
  #[dbl 120 (DC.quotGens.getD 0 #[]) (qiArr r 0), dbl 120 (DC.quotGens.getD 1 #[]) (qiArr r 1)]

theorem pgD_eq (r : QuotRecord) : pairGens r = pgD r := by
  unfold pairGens qgArr pgD
  rw [localCert_eq]

theorem bfs_facts {r : QuotRecord} {G T PL POS SRT SRI : Nat → Nat} {k cnt : Nat}
    (hc : (gensK (pgD r) 240 8 k G && penumHdK (pidn 240 8) cnt 50000 T PL &&
      Nat.beq cnt 40320) = true)
    (hs : ∀ s < 20, CFSG.KS.PEnumL.penumSlL 240 8 (mask 8) G k cnt T PL POS SRT SRI
      (Nat.mul s 2016) 2016 = true) :
    treeOK (leftStep 240 (pairGens r)) 2 pairRoot
        (bfs (leftStep 240 (pairGens r)) 2 pairRoot 50000) = true ∧
      (bfs (leftStep 240 (pairGens r)) 2 pairRoot 50000).tabs.size = 40320 := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hg, hh⟩, hn⟩ := hc
  have hcnt : cnt = 40320 := Nat.eq_of_beq_eq_true hn
  have hl : ∀ i < cnt, CFSG.KS.PEnumL.penumPtL 240 8 (mask 8) G k cnt T PL POS SRT SRI i =
      true := by
    intro i hi
    have hs' : i / 2016 < 20 := by omega
    exact CFSG.KS.PEnumL.penumSlL_spec (hs (i / 2016) hs') i (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega) hi
  rw [← pgD_eq] at hg
  have hp : ∀ i < cnt, penumPtK 240 8 (mask 8) (240 * 8) false G G k cnt T PL POS SRT SRI i =
      true :=
    CFSG.KS.PEnumL.penumPtK_of_L szOK8 (fun j hj => ((gensOK_of hg).2 j hj).2) hh hl
  obtain ⟨h1, h2⟩ := penumK_left_sound (cap := 50000) szOK8 (gensOK_of hg) hh hp
  rw [root_eq]
  change treeOK (leftStep 240 (pairGens r)) (pairGens r).size (idTab 240)
      (enumBFS 240 (pairGens r) 50000) = true ∧ (enumBFS 240 (pairGens r) 50000).tabs.size = 40320
  rw [h1]
  exact ⟨h2, by simp [penumRec, hcnt]⟩

theorem c0 : (gensK (pgD (DC.records.getD 0 default)) 240 8 R0.k R0.G &&
    penumHdK (pidn 240 8) R0.cnt 50000 R0.T R0.PL && Nat.beq R0.cnt 40320) = true := by quickRfl
theorem c1 : (gensK (pgD (DC.records.getD 1 default)) 240 8 R1.k R1.G &&
    penumHdK (pidn 240 8) R1.cnt 50000 R1.T R1.PL && Nat.beq R1.cnt 40320) = true := by quickRfl
theorem c2 : (gensK (pgD (DC.records.getD 2 default)) 240 8 R2.k R2.G &&
    penumHdK (pidn 240 8) R2.cnt 50000 R2.T R2.PL && Nat.beq R2.cnt 40320) = true := by quickRfl
theorem c3 : (gensK (pgD (DC.records.getD 3 default)) 240 8 R3.k R3.G &&
    penumHdK (pidn 240 8) R3.cnt 50000 R3.T R3.PL && Nat.beq R3.cnt 40320) = true := by quickRfl
theorem c4 : (gensK (pgD (DC.records.getD 4 default)) 240 8 R4.k R4.G &&
    penumHdK (pidn 240 8) R4.cnt 50000 R4.T R4.PL && Nat.beq R4.cnt 40320) = true := by quickRfl
theorem c5 : (gensK (pgD (DC.records.getD 5 default)) 240 8 R5.k R5.G &&
    penumHdK (pidn 240 8) R5.cnt 50000 R5.T R5.PL && Nat.beq R5.cnt 40320) = true := by quickRfl
theorem c6 : (gensK (pgD (DC.records.getD 6 default)) 240 8 R6.k R6.G &&
    penumHdK (pidn 240 8) R6.cnt 50000 R6.T R6.PL && Nat.beq R6.cnt 40320) = true := by quickRfl
theorem c7 : (gensK (pgD (DC.records.getD 7 default)) 240 8 R7.k R7.G &&
    penumHdK (pidn 240 8) R7.cnt 50000 R7.T R7.PL && Nat.beq R7.cnt 40320) = true := by quickRfl
theorem c8 : (gensK (pgD (DC.records.getD 8 default)) 240 8 R8.k R8.G &&
    penumHdK (pidn 240 8) R8.cnt 50000 R8.T R8.PL && Nat.beq R8.cnt 40320) = true := by quickRfl
theorem c9 : (gensK (pgD (DC.records.getD 9 default)) 240 8 R9.k R9.G &&
    penumHdK (pidn 240 8) R9.cnt 50000 R9.T R9.PL && Nat.beq R9.cnt 40320) = true := by quickRfl
theorem c10 : (gensK (pgD (DC.records.getD 10 default)) 240 8 R10.k R10.G &&
    penumHdK (pidn 240 8) R10.cnt 50000 R10.T R10.PL && Nat.beq R10.cnt 40320) = true := by
  quickRfl
theorem c11 : (gensK (pgD (DC.records.getD 11 default)) 240 8 R11.k R11.G &&
    penumHdK (pidn 240 8) R11.cnt 50000 R11.T R11.PL && Nat.beq R11.cnt 40320) = true := by
  quickRfl

theorem bfs_ok : ∀ k < 12,
    treeOK (leftStep 240 (pairGens (DC.records.getD k default))) 2 pairRoot
        (bfs (leftStep 240 (pairGens (DC.records.getD k default))) 2 pairRoot 50000) = true ∧
      (bfs (leftStep 240 (pairGens (DC.records.getD k default))) 2 pairRoot 50000).tabs.size =
        40320 := by
  intro k hk
  interval_cases k
  · exact bfs_facts c0 sl0All
  · exact bfs_facts c1 sl1All
  · exact bfs_facts c2 sl2All
  · exact bfs_facts c3 sl3All
  · exact bfs_facts c4 sl4All
  · exact bfs_facts c5 sl5All
  · exact bfs_facts c6 sl6All
  · exact bfs_facts c7 sl7All
  · exact bfs_facts c8 sl8All
  · exact bfs_facts c9 sl9All
  · exact bfs_facts c10 slAAll
  · exact bfs_facts c11 slBAll

theorem allBelowN_of {n : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) : allBelowN n p = true := by
  unfold allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨i, hi⟩ -
  exact h i hi

theorem rec_ok {k : Nat} (hk : k < 12) :
    recordCheck (indexOf m120Enum.tabs) (DC.records.getD k default) = true := by
  obtain ⟨ht, hs⟩ := bfs_ok k hk
  unfold recordCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨allBelowN_of fun j hj => found_rec k hk j hj, ht⟩, hs⟩,
    allBelowN_of fun m hm => rec_words k hk m hm⟩

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
  have h := rec_ok hk'
  rwa [List.getD_eq_getElem _ _ hk] at h

end CertificateChecks.KernelSpor.ON2127

end
