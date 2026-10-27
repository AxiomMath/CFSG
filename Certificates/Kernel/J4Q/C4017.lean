module

public import CFSG.Sporadic.J4.QTNative
public import Certificates.Kernel.J4Q.C4017Mat
public import Certificates.Kernel.J4Q.C4010
import Certificates.Kernel.J4Q.Strs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.SGW CFSG.Sporadic.J4.QT.sgWords
#j4q_strs CFSG.KD.J4Q.CHL CFSG.Sporadic.J4.QT.chainLevels

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] noncomputable def mkAllPts (l : List (Nat × List Int)) (f : Nat × List Int → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih => andB (f p) ih) l

theorem mkAllPts_spec {f : Nat × List Int → Bool} : ∀ {l : List (Nat × List Int)},
    mkAllPts l f = true → ∀ p ∈ l, f p = true
  | [], _ => by simp
  | p :: l, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h1
    · exact mkAllPts_spec h2 q hq

@[expose] noncomputable def mkPtOK (r : Nat) (p : Nat × List Int) : Bool :=
  p.2.all (fun ℓ => letters.contains ℓ) &&
    p.2.foldr (fun ℓ c => actN 11 (letterRows.getD (letters.idxOf ℓ) []) c) r == p.1

theorem pts0_chk : mkAllPts (ptsK OR.s0) (mkPtOK 1) = true := by quickRfl

theorem pts1_chk : mkAllPts (ptsK OR.s1) (mkPtOK 3) = true := by quickRfl

theorem ptOK_spec {r : Nat} {p : Nat × List Int} (h : mkPtOK r p = true) :
    (∀ ℓ ∈ p.2, ℓ ∈ letters) ∧ p.2.foldr act r = p.1 := by
  unfold mkPtOK at h
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  have e : act = fun ℓ c => actN 11 (letterRows.getD (letters.idxOf ℓ) []) c := by
    funext ℓ c
    exact act_eq ℓ c
  exact ⟨fun ℓ hℓ => List.contains_iff_mem.1 (h.1 ℓ hℓ), by rw [e]; exact h.2⟩

theorem mem_fsts {c : Nat} {l : List (Nat × List Int)} (h : c ∈ fstsK l) : ∃ p ∈ l, p.1 = c := by
  rw [fstsK_eq] at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact ⟨p, hp, rfl⟩

@[expose] noncomputable def mkBasisOK (ps : List (Nat × List Int)) (L : List (List Nat)) : Bool :=
  strictB (mkSet (fstsK ps)) fun S => (List.range 11).all fun j =>
    (L.getD j []).all (fun c => bitB S c) && (L.getD j []).foldl (· ^^^ ·) 0 == 2 ^ j

theorem basisOK_spec {ps : List (Nat × List Int)} {L : List (List Nat)} (h : mkBasisOK ps L = true) :
    ∀ j < 11, (∀ c ∈ L.getD j [], ∃ p ∈ ps, p.1 = c) ∧ (L.getD j []).foldl (· ^^^ ·) 0 = 2 ^ j := by
  intro j hj
  unfold mkBasisOK at h
  rw [mkStrictB_eq, List.all_eq_true] at h
  have h' := h j (List.mem_range.2 hj)
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h'
  refine ⟨fun c hc => mem_fsts ?_, h'.2⟩
  rw [mem_mkSet, ← bitB_eq]
  exact h'.1 c hc

theorem orbits_eq : orbits = [(1, ptsK OR.s0, [[1], [2], [4], [8], [16], [32], [64], [128],
    [1, 2, 16, 32, 64, 925, 1087, 1745], [2, 4, 8, 32, 64, 128, 1087, 1745], [1, 2, 4, 8, 16, 32, 1087]]),
   (3, ptsK OR.s1,
    [[3, 72, 641, 715], [72, 641, 715], [18, 36, 72, 301, 715, 924], [36, 72, 715, 924, 1056, 1299],
    [18, 72, 641, 715], [18, 72, 301, 715, 924], [36, 715, 924, 1056, 1299], [3, 36, 72, 301, 450],
    [3, 301, 641, 924, 1056, 1299], [36, 301, 450, 715], [18, 72, 301, 715, 924, 1056]])] := by
  rw [OR.eq]
  simp only [ptsOfString_ofList]

theorem basis_chk : andB (mkBasisOK (ptsK OR.s0) [[1], [2], [4], [8], [16], [32], [64], [128],
    [1, 2, 16, 32, 64, 925, 1087, 1745], [2, 4, 8, 32, 64, 128, 1087, 1745], [1, 2, 4, 8, 16, 32, 1087]])
    (mkBasisOK (ptsK OR.s1)
    [[3, 72, 641, 715], [72, 641, 715], [18, 36, 72, 301, 715, 924], [36, 72, 715, 924, 1056, 1299],
    [18, 72, 641, 715], [18, 72, 301, 715, 924], [36, 715, 924, 1056, 1299], [3, 36, 72, 301, 450],
    [3, 301, 641, 924, 1056, 1299], [36, 301, 450, 715], [18, 72, 301, 715, 924, 1056]]) = true := by
  quickRfl

theorem words_chk : decide ((∀ j ∈ List.range 11, ∀ ℓ ∈ uWordK j, ℓ ∈ letters) ∧
    ∀ ℓ ∈ mkXPW, ℓ ∈ letters) = true := by
  quickRfl

@[expose] noncomputable def mkActL (ℓ : Int) (c : Nat) : Nat := actN 11 (letterRows.getD (letters.idxOf ℓ) []) c

@[expose] noncomputable def mkActS (i c : Nat) : Nat := actN 11 (sgRows.getD i []) c

theorem act_fun : act = mkActL := by
  funext ℓ c
  exact act_eq ℓ c

theorem actS_fun : actS = mkActS := by
  funext i c
  unfold actS sgRow mkActS
  exact rowsXor_eq _ _ 11

@[expose] noncomputable def mkSGW : List (List Int) :=
  [lettersK SGW.s0, lettersK SGW.s1, lettersK SGW.s2, lettersK SGW.s3, lettersK SGW.s4,
    lettersK SGW.s5, lettersK SGW.s6, lettersK SGW.s7, lettersK SGW.s8, lettersK SGW.s9,
    lettersK SGW.s10, lettersK SGW.s11]

theorem sgWords_eq : sgWords = mkSGW := by
  rw [SGW.eq]
  simp only [lettersOfString_ofList]
  rfl

@[expose] noncomputable def mkCHL : List (List (List Nat)) :=
  [idxK CHL.s0, idxK CHL.s1, idxK CHL.s2, idxK CHL.s3, idxK CHL.s4]

theorem chainLevels_eq : chainLevels = mkCHL := by
  rw [CHL.eq]
  simp only [idxWordsOfString_ofList]
  rfl

theorem sgLet_chk : (mkSGW.all fun w => w.all fun ℓ => letters.contains ℓ) = true := by quickRfl

@[expose] noncomputable def mkSG (i : Nat) : Bool :=
  (List.range 11).all fun j => (sgRows.getD i []).getD j 0 == (mkSGW.getD i []).foldr mkActL (2 ^ j)

#j4q_all CFSG.KD.J4Q.SGC CertificateChecks.KernelJ4Q.mkSG 12

@[expose] noncomputable def mkCH (j : Nat) : Bool :=
  ((mkCHL.getD j []).all fun tw => tw.all (fun i => Nat.blt i 12) &&
    (List.range j).all fun i => tw.foldr mkActS (CFSG.Sporadic.J4.QT.chainBase.getD i 0) == CFSG.Sporadic.J4.QT.chainBase.getD i 0) &&
  mkNodup ((mkCHL.getD j []).map fun tw => tw.foldr mkActS (CFSG.Sporadic.J4.QT.chainBase.getD j 0)) &&
    allLtK 2048 ((mkCHL.getD j []).map fun tw => tw.foldr mkActS (CFSG.Sporadic.J4.QT.chainBase.getD j 0))

#j4q_all CFSG.KD.J4Q.CHC CertificateChecks.KernelJ4Q.mkCH 5

theorem chainLen_chk : Nat.beq ((mkCHL.getD 0 []).length * (mkCHL.getD 1 []).length *
    (mkCHL.getD 2 []).length * (mkCHL.getD 3 []).length * (mkCHL.getD 4 []).length) 244823040 = true := by
  quickRfl

theorem letters_neg : decide (∀ ℓ ∈ letters, -ℓ ∈ letters) = true := by quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem c4017 : (∀ ℓ ∈ letters, -ℓ ∈ letters)
    ∧ (∀ o ∈ orbits, ∀ p ∈ o.2.1,
          (∀ ℓ ∈ p.2, ℓ ∈ letters) ∧ p.2.foldr act o.1 = p.1)
    ∧ (∀ c < 2 ^ 11, c ≠ 0 → ∃ o ∈ orbits, ∃ p ∈ o.2.1, p.1 = c)
    ∧ (∀ o ∈ orbits, ∀ j < 11,
          (∀ c ∈ o.2.2.getD j [], ∃ p ∈ o.2.1, p.1 = c) ∧
            (o.2.2.getD j []).foldl (· ^^^ ·) 0 = 2 ^ j)
    ∧ ((∀ j < 11, ∀ ℓ ∈ uWord j, ℓ ∈ letters) ∧ ∀ ℓ ∈ xpWord, ℓ ∈ letters)
    ∧ (∀ w ∈ sgWords, ∀ ℓ ∈ w, ℓ ∈ letters)
    ∧ (∀ i < 12, ∀ j < 11,
          sgRow i j = (sgWords.getD i []).foldr act (2 ^ j))
    ∧ (∀ j < 5, ∀ tw ∈ chainLevels.getD j [], (∀ i ∈ tw, i < 12) ∧
          ∀ i < j, tw.foldr actS (CFSG.Sporadic.J4.QT.chainBase.getD i 0) = CFSG.Sporadic.J4.QT.chainBase.getD i 0)
    ∧ (∀ j < 5,
          ((chainLevels.getD j []).map fun tw => tw.foldr actS (CFSG.Sporadic.J4.QT.chainBase.getD j 0)).Nodup ∧
            ∀ tw ∈ chainLevels.getD j [], tw.foldr actS (CFSG.Sporadic.J4.QT.chainBase.getD j 0) < 2 ^ 11)
    ∧ ((chainLevels.getD 0 []).length * (chainLevels.getD 1 []).length *
          (chainLevels.getD 2 []).length * (chainLevels.getD 3 []).length *
          (chainLevels.getD 4 []).length = 244823040)
    ∧ (chkU (locMats ()) (locInvs ()) = true)
    ∧ (chkConj (locMats ()) (locInvs ()) = true)
    ∧ (chkFree (locMats ()) (locInvs ()) = true)
    ∧ (chkOut (locMats ()) (locInvs ()) = true)
    ∧ (chkFus (locMats ()) (locInvs ()) = true) := by
  obtain ⟨w1, w2⟩ := of_decide_eq_true words_chk
  obtain ⟨b0, b1⟩ := andB_true basis_chk
  refine ⟨of_decide_eq_true letters_neg, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, chkU_ok,
    chkConj_ok, chkFree_ok, chkOut_ok, chkFus_ok⟩
  · rw [orbits_eq]
    intro o ho p hp
    rcases List.mem_cons.1 ho with rfl | ho
    · exact ptOK_spec (mkAllPts_spec pts0_chk p hp)
    · rcases List.mem_cons.1 ho with rfl | ho
      · exact ptOK_spec (mkAllPts_spec pts1_chk p hp)
      · simp at ho
  · intro c hc h0
    have h := mem_of_mkSet_eq mk4010_chk (List.mem_range'_1.2 ⟨Nat.pos_of_ne_zero h0, by simpa using hc⟩)
    rw [orbits_eq]
    rcases List.mem_append.1 h with h | h
    · exact ⟨_, List.mem_cons_self, mem_fsts h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, mem_fsts h⟩
  · rw [orbits_eq]
    intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · exact basisOK_spec b0
    · rcases List.mem_cons.1 ho with rfl | ho
      · exact basisOK_spec b1
      · simp at ho
  · intro j hj ℓ hℓ
    rw [uWord_eq] at hℓ
    exact w1 j (List.mem_range.2 hj) ℓ hℓ
  · rw [xpWord_eq]
    exact w2
  · rw [sgWords_eq]
    intro w hw ℓ hℓ
    exact List.contains_iff_mem.1 (List.all_eq_true.1 (List.all_eq_true.1 sgLet_chk w hw) ℓ hℓ)
  · intro i hi j hj
    have h := SGC.all i hi
    unfold mkSG at h
    rw [List.all_eq_true] at h
    have := beq_iff_eq.1 (h j (List.mem_range.2 hj))
    rw [sgWords_eq, act_fun]
    exact this
  · intro j hj tw htw
    have h := CHC.all j hj
    unfold mkCH at h
    simp only [Bool.and_eq_true] at h
    rw [chainLevels_eq] at htw
    have g := List.all_eq_true.1 h.1.1 tw htw
    rw [Bool.and_eq_true] at g
    refine ⟨fun i hi => mkLt (List.all_eq_true.1 g.1 i hi), fun i hi => ?_⟩
    rw [actS_fun]
    exact beq_iff_eq.1 (List.all_eq_true.1 g.2 i (List.mem_range.2 hi))
  · intro j hj
    have h := CHC.all j hj
    unfold mkCH at h
    simp only [Bool.and_eq_true] at h
    rw [chainLevels_eq, actS_fun]
    refine ⟨nodup_of_mkNodup h.1.2, fun tw htw => ?_⟩
    have := allLtK_spec h.2 _ (List.mem_map_of_mem htw)
    simpa using this
  · rw [chainLevels_eq]
    exact Nat.eq_of_beq_eq_true chainLen_chk

end CertificateChecks.KernelJ4Q

end
