module

public import Certificates.Kernel.Sporadic.OddCore.ON2120B

public section

set_option linter.unusedSectionVars false

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2120

open CFSG.ONSchreier.Native hiding posArr
open CFSG.ONSchreier CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore
open CFSG.KS.TW CFSG.KS.PW CertificateChecks.KernelSpor.ON3 CFSG.KS
open CFSG.KC.Enum hiding pcomp
open CertificateChecks.KernelSpor.ON2119

theorem blocks_size : Data.quotientBlocks.size = 120 := by decide +kernel

theorem blocks_two : ∀ i < Data.quotientBlocks.size, Data.quotientBlocks[i]!.size = 2 := by
  decide +kernel

theorem blocks_lt : ∀ u < 2 * Data.quotientBlocks.size, bpt Data.quotientBlocks u < nPts := by
  decide +kernel

theorem blocks_distinct : ∀ u < 2 * Data.quotientBlocks.size, ∀ v < u,
    bpt Data.quotientBlocks v ≠ bpt Data.quotientBlocks u := by
  decide +kernel

theorem bPos_get {t e : Nat} (ht : t < 120) (he : e < 2) :
    bPos[(Data.quotientBlocks[t]!)[e]!]! = t := by
  have h := (blockPos_spec blocks_two blocks_lt blocks_distinct).2 (2 * t + e)
    (by rw [blocks_size]; omega)
  have e1 : bpt Data.quotientBlocks (2 * t + e) = (Data.quotientBlocks[t]!)[e]! := by
    unfold bpt
    congr 2 <;> omega
  rw [e1] at h
  rw [bPos, h]
  omega

theorem conj_size : Data.quotientConjugator.size = 120 := by decide +kernel

theorem cil_ok : ∀ x < 120, Data.quotientConjugator[x]! < 120 ∧
    cil (Data.quotientConjugator[x]!) = x ∧ cil x < 120 := by
  decide +kernel

theorem ci_get {x : Nat} (hx : x < 120) :
    (pinvCand 120 Data.quotientConjugator)[x]! = cil x := by
  rw [arr_ext conj_size fun i _ => rfl]
  exact CFSG.KS.CB.pinvCand_get (fun i hi => (cil_ok i hi).1) (fun i hi => (cil_ok i hi).2.1) hx

theorem pos120_eq (gs : Array (Array Nat)) :
    ∀ (w : List Nat) (x : Nat), x < 120 → (posArr 120 gs w)[x]! = pos120 gs w x
  | [], x, hx => pid_get' hx
  | l :: w, x, hx => by
    have e : posArr 120 gs (l :: w) = pcomp 120 (gs.getD (l - 1) (pid 120)) (posArr 120 gs w) := rfl
    rw [e, pcomp_get' hx, pos120_eq gs w x hx]
    rfl

section B


theorem blk_of {g : Array Nat} {F : Nat → Nat} {o : Nat} (hg : Good g F) (h : blkP F o = true) :
    (∀ i < 120, (bTab g)[i]! = bw o i) ∧
      blockImgOK g Data.quotientBlocks (bTab g) = true := by
  have hb : ∀ i < 120, bw o i < 120 ∧ inBlock Data.quotientBlocks[bw o i]!
      (F (Data.quotientBlocks[i]!)[0]!) = true ∧ inBlock Data.quotientBlocks[bw o i]!
      (F (Data.quotientBlocks[i]!)[1]!) = true := by
    intro i hi
    have := List.all_eq_true.1 h i (List.mem_range.2 hi)
    simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using this
  have hpt : ∀ i < 120, ∀ e < 2, (Data.quotientBlocks[i]!)[e]! < 245520 := by
    intro i hi e he
    have := blocks_lt (2 * i + e) (by rw [blocks_size]; omega)
    unfold bpt at this
    have e1 : (2 * i + e) / 2 = i := by omega
    have e2 : (2 * i + e) % 2 = e := by omega
    rwa [e1, e2] at this
  have hval : ∀ i < 120, g[(Data.quotientBlocks[i]!)[0]!]! = F (Data.quotientBlocks[i]!)[0]! ∧
      g[(Data.quotientBlocks[i]!)[1]!]! = F (Data.quotientBlocks[i]!)[1]! := fun i hi =>
    ⟨(hg.2.2 _ (hpt i hi 0 (by norm_num))).1, (hg.2.2 _ (hpt i hi 1 (by norm_num))).1⟩
  have htab : ∀ i < 120, (bTab g)[i]! = bw o i := by
    intro i hi
    unfold bTab blockTab
    rw [getElem!_pos _ i (by simp [blocks_size]; exact hi), Array.getElem_map,
      ← getElem!_pos _ i (by rw [blocks_size]; exact hi), (hval i hi).1]
    obtain ⟨ht, h0, -⟩ := hb i hi
    unfold inBlock at h0
    simp only [Bool.or_eq_true, beq_iff_eq] at h0
    rcases h0 with h0 | h0
    · rw [← h0]; exact bPos_get ht (by norm_num)
    · rw [← h0]; exact bPos_get ht (by norm_num)
  refine ⟨htab, ?_⟩
  unfold blockImgOK
  rw [allBelowN_iff]
  intro i hi
  rw [blocks_size] at hi
  rw [htab i hi, (hval i hi).1, (hval i hi).2, blocks_size]
  obtain ⟨ht, h0, h1⟩ := hb i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨ht, h0⟩, h1⟩

theorem pi_of {g arr : Array Nat} {o : Nat} {T : Nat → Nat} (hb : ∀ i < 120, (bTab g)[i]! = bw o i)
    (hT : ∀ x < 120, arr[x]! = T x) (h : piP o T = true) : peq 120 (piArr g) arr = true := by
  unfold peq piArr
  rw [allBelowN_iff]
  intro x hx
  rw [pcomp_get' hx, pcomp_get' hx, ci_get hx, hb _ (cil_ok x hx).2.2, hT x hx]
  have := List.all_eq_true.1 h x (List.mem_range.2 hx)
  simpa only [Nat.beq_eq, beq_iff_eq] using this

theorem hA_good : ∀ i < (wordArrs Data.MWords).size, Good (wordArrs Data.MWords)[i]! (hF i) :=
  fun i hi => good_hA (by rwa [mwords_size] at hi)

theorem lw_get {lwr : List (List Nat)} (hl : lwr.length = 3) {j : Nat} (hj : j < 3) :
    ((lwr.map (posArr nPts (wordArrs Data.MWords))).toArray)[j]! =
      posArr nPts (wordArrs Data.MWords) (lwr.getD j []) := by
  rw [getElem!_pos _ j (by simp [hl, hj])]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < lwr.length)]

theorem good_lw {lwr : List (List Nat)} (hl : lwr.length = 3) {j : Nat} (hj : j < 3) :
    Good ((lwr.map (posArr nPts (wordArrs Data.MWords))).toArray)[j]! (lwF lwr j) := by
  rw [lw_get hl hj]
  have h := good_posArr hA_good (lwr.getD j [])
  rwa [mwords_size] at h

theorem good_cand {lwr : List (List Nat)} (hl : lwr.length = 3) (a : Nat) {j : Nat} (hj : j < 3) :
    Good (candImgs ((lwr.map (posArr nPts (wordArrs Data.MWords))).toArray) a)[j]!
      (candG lwr a j) := by
  have hc := good_pcomp (good_lw hl hj) (good_qPow (ex a j))
  have e : candG lwr a j = fun x => lwF lwr j (Nat.repeat QT (ex a j) x) := by funext x; rfl
  rw [e]
  interval_cases j
  · simpa [candImgs, ex] using hc
  · simpa [candImgs, ex] using hc
  · simpa [candImgs, ex] using hc

theorem cands_size (lw : Array (Array Nat)) (a : Nat) : (candImgs lw a).size = 3 := rfl

theorem candOK_of {lwr : List (List Nat)} (hl : lwr.length = 3) {r : QuotRecord} {a : Nat}
    {c : Cand} (h : candP lwr r a c = true) :
    candOK (wordArrs Data.MWords) ((lwr.map (posArr nPts (wordArrs Data.MWords))).toArray) r a c =
      true := by
  cases c with
  | lift i =>
    simp only [candP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    simp only [candOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h.1, ?_⟩
    rw [allBelowN_iff]
    intro j hj
    have hb := h.2 j hj
    unfold b3 at hb
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Nat.beq_eq] at hb
    have hp := good_posArr hA_good ((r.lifts.getD i default).words.getD j [])
    rw [mwords_size] at hp
    exact peq_good hp (good_cand hl a hj) hb.1 hb.2.1 hb.2.2
  | rel w w' =>
    simp only [candP, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hgs : ∀ i < (candImgs ((lwr.map (posArr nPts (wordArrs Data.MWords))).toArray) a).size,
        Good (candImgs ((lwr.map (posArr nPts (wordArrs Data.MWords))).toArray) a)[i]!
          (candG lwr a i) := fun i hi => good_cand hl a (by rwa [cands_size] at hi)
    have e1 : ∀ v p, p < 245520 → posPt (wordArrs Data.MWords) v p = wordF 3 hF v p := by
      intro v p hp
      have := (posPt_eq hA_good v p hp).1
      rwa [mwords_size] at this
    have e2 : ∀ v p, p < 245520 → posPt (candImgs ((lwr.map (posArr nPts
        (wordArrs Data.MWords))).toArray) a) v p = wordF 3 (candG lwr a) v p := by
      intro v p hp
      have := (posPt_eq hgs v p hp).1
      rwa [cands_size] at this
    simp only [candOK, Bool.and_eq_true]
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩
    · simp only [base3Arr, List.all_toArray]
      rw [List.all_eq_true] at h3 ⊢
      intro p hp
      have hp' : p < 245520 := by simp at hp; omega
      rw [e1 w p hp', e1 w' p hp', beq_iff_eq]
      exact Nat.eq_of_beq_eq_true (h3 p hp)
    · simp only [base3Arr, List.any_toArray]
      rw [List.any_eq_true] at h4 ⊢
      obtain ⟨p, hp, hne⟩ := h4
      have hp' : p < 245520 := by simp at hp; omega
      refine ⟨p, hp, ?_⟩
      rw [e2 w p hp', e2 w' p hp', bne_iff_ne]
      intro hab
      rw [hab, Nat.beq_refl] at hne
      exact absurd hne (by decide)

theorem candCheck_of {r : QuotRecord} {lwr : List (List Nat)} {cs : List Cand} {k : Nat}
    (h : candCheckP r lwr cs k = true) :
    candCheck (wordArrs Data.MWords) r lwr cs = true := by
  simp only [candCheckP, let3, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hl, hlet⟩, hb⟩, hcs⟩, hc⟩ := h
  simp only [candCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨hl, hlet⟩, ?_⟩, hcs⟩, fun a ha => candOK_of hl (hc a ha)⟩
  rw [allBelowN_iff]
  intro i hi
  obtain ⟨hbl, hpi⟩ := hb i hi
  obtain ⟨htab, hok⟩ := blk_of (good_lw hl hi) hbl
  rw [Bool.and_eq_true]
  exact ⟨hok, pi_of htab (fun x hx => pos120_eq _ _ x hx) hpi⟩

theorem candidatesCheck_of (hh : headP CLit LLit = true)
    (hr : ∀ k < 12, candCheckP (CLit.records.getD k default) (LLit.lw.getD k [])
      (LLit.cands.getD k []) k = true) :
    candidatesCheck (wordArrs Data.MWords) = true := by
  simp only [headP, let3, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hh
  obtain ⟨⟨⟨⟨hq, hqb⟩, hg⟩, hlw⟩, hcs⟩ := hh
  unfold candidatesCheck
  rw [liftData_eq]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨hq, ?_⟩, mwords_size⟩, ?_⟩, hlw⟩, hcs⟩, fun k hk => ?_⟩
  · unfold b3 at hqb
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Nat.beq_eq] at hqb
    have hp := good_posArr hA_good LLit.qWord
    rw [mwords_size] at hp
    exact peq_good hp (good_tab (good_word (w := Data.centerGeneratorWord) (by decide)) q_get)
      hqb.1 hqb.2.1 hqb.2.2
  · rw [allBelowN_iff]
    intro i hi
    obtain ⟨hbl, hpi⟩ := hg i hi
    obtain ⟨htab, hok⟩ := blk_of (good_hA hi) hbl
    rw [Bool.and_eq_true]
    refine ⟨hok, pi_of htab (fun x hx => ?_) hpi⟩
    rw [pos120_eq _ _ x hx, qgArr, qgArr, localCert_eq]
  · rw [localCert_eq]
    exact candCheck_of (hr k hk)

end B

end CertificateChecks.KernelSpor.ON2120

end
