module

public import Certificates.Kernel.SporSch.Ly.BSData
public import CFSG.Certificates.Kernel.SporSch.LyMatSound
public import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyBSF

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS

local notation "U" X:max => unpackL 111 12 1332 X

theorem andOf {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h Bool.false_ne_true

theorem hv {X : Nat} (h : vld X = true) : validM 5 (111 * 1332) L H X = true := h

theorem mulE {X Y : Nat} (hX : vld X = true) (hY : vld Y = true) :
    mulM 5 111 (U X) (U Y) = U (mul X Y) := (mulR_eq consts (hv hX) (hv hY)).1

theorem mulV {X Y : Nat} (hX : vld X = true) (hY : vld Y = true) : vld (mul X Y) = true :=
  (mulR_eq consts (hv hX) (hv hY)).2

theorem idE : idM 111 = U ONE := (idM_eq consts).1

theorem vOne : vld ONE = true := (idM_eq consts).2

theorem beqE {X Y : Nat} (hX : vld X = true) (hY : vld Y = true) :
    (U X == U Y) = Nat.beq X Y := beq_eq consts (hv hX) (hv hY)

theorem bl {i k : Nat} (h : i < k) : Nat.blt i k = true := Nat.blt_eq.mpr h

theorem bl' {i k : Nat} (h : ¬ i < k) : Nat.blt i k = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.blt_eq.mp h')

theorem matA_eq : matA = U A := by
  have e : matA = rowsOf 5 111 seedA := rfl
  rw [e, LySA.eq, payRunP_eq (w := 12) (S := 1332) _ (by norm_num) (by norm_num) (by norm_num),
    Nat.eq_of_beq_eq_true payA]

theorem matB_eq : matB = U B := by
  have e : matB = rowsOf 5 111 seedB := rfl
  rw [e, LySB.eq, payRunP_eq (w := 12) (S := 1332) _ (by norm_num) (by norm_num) (by norm_num),
    Nat.eq_of_beq_eq_true payB]

theorem b4_eq : powM 5 111 matB 4 = U B4 := by
  rw [matB_eq]
  rw [(powM_eq consts (hv vB) 4).1, Nat.eq_of_beq_eq_true pB4]

theorem chain {G GI K : Nat → Nat} {W : List Int} {m c : Nat}
    (h : ∀ k < m, Nat.beq (wordR 5 12 1332 111 8 L H CM RM G GI (K k)
      (List.take c (List.drop (Nat.mul k c) W))) (K (Nat.succ k)) = true)
    (hl : W.length ≤ m * c) :
    wordR 5 12 1332 111 8 L H CM RM G GI (K 0) W = K m := by
  have key : ∀ j ≤ m, wordR 5 12 1332 111 8 L H CM RM G GI (K (m - j))
      (W.drop ((m - j) * c)) = K m := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le hl]
      rfl
    | succ j ih =>
      intro hj
      have e : m - j = (m - (j + 1)) + 1 := by omega
      have hk := Nat.eq_of_beq_eq_true (h (m - (j + 1)) (by omega))
      rw [← List.take_append_drop c (W.drop ((m - (j + 1)) * c)), wordR_append,
        List.drop_drop]
      have hm : Nat.mul (m - (j + 1)) c = (m - (j + 1)) * c := rfl
      rw [hm] at hk
      rw [hk, ← ih (by omega), e, Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
  have := key m le_rfl
  rwa [Nat.sub_self, Nat.zero_mul, List.drop_zero] at this

def Rep (acc : Array (Mat × Mat)) (k : Nat) : Prop :=
  acc.size = k ∧ ∀ i < k, acc[i]! = (U (CF i), U (CI i))

theorem vCFi {i : Nat} (hi : i < 12) : vld (CF i) = true ∧ vld (CI i) = true :=
  (bAnd_iff _ _).1 (allN_spec vCF i hi)

theorem vCFx {k : Nat} (hk : k ≤ 12) (i : Nat) : vld (CFx k i) = true ∧ vld (CIx k i) = true := by
  unfold CFx CIx
  by_cases h : i < k
  · rw [bl h]
    exact vCFi (by omega)
  · rw [bl' h]
    exact ⟨vOne, vOne⟩

theorem pairAt_rep {acc : Array (Mat × Mat)} {k : Nat} (h : Rep acc k) (i : Nat) :
    pairAt acc i = (U (CFx k i), U (CIx k i)) := by
  have hs := h.1
  unfold pairAt CFx CIx
  by_cases hi : i < k
  · rw [bl hi, ← h.2 i hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
      Option.getD_some, getElem!_pos acc i (by omega)]
  · rw [bl' hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none,
      idE]

theorem word_of {G GI : Nat → Nat} {g gi : Nat → Mat} (hg : ∀ i, g i = U (G i))
    (hgi : ∀ i, gi i = U (GI i)) (hG : ∀ i, vld (G i) = true) (hGI : ∀ i, vld (GI i) = true)
    (w : List Int) :
    evalWordM g gi w = U (wordR 5 12 1332 111 8 L H CM RM G GI ONE w) ∧
      vld (wordR 5 12 1332 111 8 L H CM RM G GI ONE w) = true := by
  have e : evalWordM g gi w = wordFromM g gi (idM 111) w := rfl
  rw [e, idE]
  exact wordFromM_eq consts (fun i => ⟨hg i, hG i⟩) (fun i => ⟨hgi i, hGI i⟩) (hv vOne) w

theorem extend_rep : ∀ (ws : List (List Int)) (acc : Array (Mat × Mat)) (k : Nat),
    Rep acc k → k + ws.length ≤ 12 →
    (∀ t < ws.length, Nat.beq (wordR 5 12 1332 111 8 L H CM RM (CFx (k + t)) (CIx (k + t)) ONE
      (ws.getD t [])) (CF (k + t)) = true) →
    Rep (extendM acc ws) (k + ws.length)
  | [], acc, k, h, _, _ => h
  | w :: vs, acc, k, h, hk, hw => by
    have e : extendM acc (w :: vs) = extendM (acc.push
        (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w,
          invM 5 111 (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w))) vs :=
      rfl
    have hlen : (w :: vs).length = vs.length + 1 := rfl
    have hs := h.1
    have hk' : k < 12 := by omega
    obtain ⟨hX, _⟩ := word_of (G := CFx k) (GI := CIx k) (g := fun i => (pairAt acc i).1)
      (gi := fun i => (pairAt acc i).2) (fun i => by rw [pairAt_rep h i])
      (fun i => by rw [pairAt_rep h i]) (fun i => (vCFx (by omega) i).1)
      (fun i => (vCFx (by omega) i).2) w
    have h0 := hw 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    rw [Nat.eq_of_beq_eq_true h0] at hX
    have hinv : invM 5 111 (U (CF k)) = U (CI k) :=
      invM_eq (by norm_num) consts (hv (vCFi hk').1) (hv (vCFi hk').2)
        (allN_spec iCF k hk')
    have hrep : Rep (acc.push (U (CF k), U (CI k))) (k + 1) := by
      refine ⟨by rw [Array.size_push, h.1], fun i hi => ?_⟩
      rcases Nat.lt_or_ge i k with hik | hik
      · rw [getElem!_pos _ i (by rw [Array.size_push, h.1]; omega), Array.getElem_push_lt (by omega),
          ← getElem!_pos acc i (by omega), h.2 i hik]
      · have : i = k := by omega
        subst this
        rw [getElem!_pos _ i (by rw [Array.size_push, h.1]; omega)]
        simp [Array.getElem_push, hs]
    rw [e, hX, hinv, hlen, ← Nat.add_assoc, Nat.add_right_comm]
    refine extend_rep vs _ (k + 1) hrep (by omega) fun t ht => ?_
    have := hw (t + 1) (by simp; omega)
    simp only [List.getD_cons_succ] at this
    rw [Nat.add_right_comm k 1 t]
    exact this

theorem c0_eq : evalWordM seedM (seedMInv (U B4)) seedWord0 = U (CF 0) := by
  have hg : ∀ i, seedM i = U (GS i) := fun i => by
    cases i with
    | zero => exact matA_eq
    | succ i => exact matB_eq
  have hgi : ∀ i, seedMInv (U B4) i = U (GSI i) := fun i => by
    cases i with
    | zero => exact matA_eq
    | succ i => rfl
  have hG : ∀ i, vld (GS i) = true := fun i => by
    cases i with
    | zero => exact vA
    | succ i => exact vB
  have hGI : ∀ i, vld (GSI i) = true := fun i => by
    cases i with
    | zero => exact vA
    | succ i => exact vB4
  have hw : seedWord0 = W0 := by
    have e : seedWord0 = parseInts seedWord0Txt := rfl
    rw [e, LyW0.eq]
    exact parseK_sound parse0
  have hm : K0.m = 84 := rfl
  have hk := Nat.eq_of_beq_eq_true k0m
  rw [hm] at hk
  rw [(word_of hg hgi hG hGI _).1, hw, ← Nat.eq_of_beq_eq_true k00,
    chain K0.all (by simpa [hm] using Nat.le_of_ble_eq_true len0), hk]

theorem c1_eq : evalWordM seedM (seedMInv (U B4)) seedWord1 = U (CF 1) := by
  have hg : ∀ i, seedM i = U (GS i) := fun i => by
    cases i with
    | zero => exact matA_eq
    | succ i => exact matB_eq
  have hgi : ∀ i, seedMInv (U B4) i = U (GSI i) := fun i => by
    cases i with
    | zero => exact matA_eq
    | succ i => rfl
  have hG : ∀ i, vld (GS i) = true := fun i => by
    cases i with
    | zero => exact vA
    | succ i => exact vB
  have hGI : ∀ i, vld (GSI i) = true := fun i => by
    cases i with
    | zero => exact vA
    | succ i => exact vB4
  have hw : seedWord1 = W1 := by
    have e : seedWord1 = parseInts seedWord1Txt := rfl
    rw [e, LyW1.eq]
    exact parseK_sound parse1
  have hm : K1.m = 124 := rfl
  have hk := Nat.eq_of_beq_eq_true k1m
  rw [hm] at hk
  rw [(word_of hg hgi hG hGI _).1, hw, ← Nat.eq_of_beq_eq_true k10,
    chain K1.all (by simpa [hm] using Nat.le_of_ble_eq_true len1), hk]

theorem cs_rep : Rep (cStarArr (U B4)) 12 := by
  have e : cStarArr (U B4) = extendM
      #[(evalWordM seedM (seedMInv (U B4)) seedWord0,
          invM 5 111 (evalWordM seedM (seedMInv (U B4)) seedWord0)),
        (evalWordM seedM (seedMInv (U B4)) seedWord1,
          invM 5 111 (evalWordM seedM (seedMInv (U B4)) seedWord1))] (cDerivations ()).toList :=
    rfl
  have i0 : invM 5 111 (U (CF 0)) = U (CI 0) :=
    invM_eq (by norm_num) consts (hv (vCFi (by omega)).1) (hv (vCFi (by omega)).2)
      (allN_spec iCF 0 (by omega))
  have i1 : invM 5 111 (U (CF 1)) = U (CI 1) :=
    invM_eq (by norm_num) consts (hv (vCFi (by omega)).1) (hv (vCFi (by omega)).2)
      (allN_spec iCF 1 (by omega))
  rw [e, c0_eq, c1_eq, i0, i1]
  have h2 : Rep #[(U (CF 0), U (CI 0)), (U (CF 1), U (CI 1))] 2 := by
    refine ⟨rfl, fun i hi => ?_⟩
    interval_cases i <;> rfl
  have hl : (cDerivations ()).toList.length = 10 := rfl
  have := extend_rep (cDerivations ()).toList _ 2 h2 (by rw [hl]) fun t ht => by
    rw [hl] at ht
    exact allN_spec der t ht
  rwa [hl] at this

theorem csCF (i : Nat) : (pairAt (cStarArr (U B4)) i).1 = U (CFx 12 i) := by
  rw [pairAt_rep cs_rep i]

theorem csCI (i : Nat) : (pairAt (cStarArr (U B4)) i).2 = U (CIx 12 i) := by
  rw [pairAt_rep cs_rep i]

theorem sylow_get {k : Nat} (hk : k < 5) :
    (sylowGens (cStarArr (U B4)))[k]! = evalWordM (fun i => (pairAt (cStarArr (U B4)) i).1)
      (fun i => (pairAt (cStarArr (U B4)) i).2) ((sylowWords ())[k]!) := by
  unfold sylowGens
  rw [getElem!_pos _ k (by simp; omega), Array.getElem_push_lt (by simp; omega)]
  simp

theorem us1_eq : (sylowGens (cStarArr (U B4)))[1]! = U U1 := by
  rw [sylow_get (by omega), (word_of csCF csCI (fun i => (vCFx le_rfl i).1)
    (fun i => (vCFx le_rfl i).2) _).1, Nat.eq_of_beq_eq_true u1]

theorem us2_eq : (sylowGens (cStarArr (U B4)))[2]! = U U2 := by
  rw [sylow_get (by omega), (word_of csCF csCI (fun i => (vCFx le_rfl i).1)
    (fun i => (vCFx le_rfl i).2) _).1, Nat.eq_of_beq_eq_true u2]

theorem cz_eq (j : Nat) : bsCzM (cStarArr (U B4)) j = U (CZ j) := by
  unfold bsCzM CZ
  by_cases h : j < 12
  · simp only [h, ↓reduceIte]
    rw [bl h, csCF, CFx, bl h]
  · simp only [h, ↓reduceIte]
    rw [bl' h, matA_eq]

theorem czi_eq (j : Nat) : bsCzMi (cStarArr (U B4)) j = U (CZI j) := by
  unfold bsCzMi CZI
  by_cases h : j < 12
  · simp only [h, ↓reduceIte]
    rw [bl h, csCI, CIx, bl h]
  · simp only [h, ↓reduceIte]
    rw [bl' h, matA_eq]

theorem vCZ (j : Nat) : vld (CZ j) = true ∧ vld (CZI j) = true := by
  unfold CZ CZI
  by_cases h : j < 12
  · rw [bl h]
    exact vCFi h
  · rw [bl' h]
    exact ⟨vA, vA⟩

theorem vTSi {i : Nat} (hi : i < 10) : vld (TS i) = true := allN_spec vTS i hi

theorem bsTM_eq {i : Nat} (hi : i < 10) : bsTM (cStarArr (U B4)) i = U (TS i) := by
  unfold bsTM
  by_cases h : i < 9
  · simp only [h, ↓reduceIte]
    rw [(word_of cz_eq czi_eq (fun j => (vCZ j).1) (fun j => (vCZ j).2) _).1,
      Nat.eq_of_beq_eq_true (allN_spec ts i h)]
  · have : i = 9 := by omega
    subst this
    simp only [Nat.lt_irrefl, ↓reduceIte]
    rw [matA_eq, Nat.eq_of_beq_eq_true ts9]

theorem vTSx (i : Nat) : vld (TSx i) = true := by
  unfold TSx
  by_cases h : i < 10
  · rw [bl h]
    exact vTSi h
  · rw [bl' h]
    exact vOne

theorem vTISx (i : Nat) : vld (TISx i) = true := by
  unfold TISx
  by_cases h : i < 9
  · rw [bl h]
    exact mulV (vTSi (by omega)) (vTSi (by omega))
  · rw [bl' h]
    by_cases h9 : i = 9
    · subst h9
      exact vA
    · rw [Bool.eq_false_iff.mpr fun h' => h9 (Nat.eq_of_beq_eq_true h')]
      exact vOne

theorem ta_eq : (fun i => (Array.ofFn (n := 10) fun i => bsTM (cStarArr (U B4)) i.val).getD i
    (idM 111)) = fun i => U (TSx i) := by
  funext i
  unfold TSx
  rw [Array.getD_eq_getD_getElem?]
  by_cases h : i < 10
  · rw [bl h, Array.getElem?_eq_getElem (by simpa using h), Option.getD_some, Array.getElem_ofFn,
      bsTM_eq h]
  · rw [bl' h, Array.getElem?_eq_none (by simpa using h), Option.getD_none, idE]

theorem tia_eq : (fun i => (Array.ofFn (n := 10) fun i => bsTMi (cStarArr (U B4)) i.val).getD i
    (idM 111)) = fun i => U (TISx i) := by
  funext i
  unfold TISx
  rw [Array.getD_eq_getD_getElem?]
  by_cases h : i < 10
  · rw [Array.getElem?_eq_getElem (by simpa using h), Option.getD_some, Array.getElem_ofFn]
    unfold bsTMi
    by_cases h9 : i < 9
    · simp only [h9, ↓reduceIte]
      rw [bl h9, bsTM_eq h, mulE (vTSi h) (vTSi h)]
    · have : i = 9 := by omega
      subst this
      simp only [Nat.lt_irrefl, ↓reduceIte]
      rw [bl' (by omega), matA_eq]
      rfl
  · rw [Array.getElem?_eq_none (by simpa using h), Option.getD_none, idE, bl' (by omega)]
    have hb : Nat.beq i 9 = false :=
      Bool.eq_false_iff.mpr fun h' => by have := Nat.eq_of_beq_eq_true h'; omega
    rw [hb]

theorem mf_eq : mulM 5 111 (mulM 5 111 (mulM 5 111 (sylowGens (cStarArr (U B4)))[2]!
    (sylowGens (cStarArr (U B4)))[1]!) (sylowGens (cStarArr (U B4)))[2]!)
    (sylowGens (cStarArr (U B4)))[1]! = U MF := by
  obtain ⟨v1, v2⟩ := andOf (a := vld U1) (b := vld U2) vU
  rw [us1_eq, us2_eq, mulE v2 v1, mulE (mulV v2 v1) v2, mulE (mulV (mulV v2 v1) v2) v1,
    Nat.eq_of_beq_eq_true mf]

theorem vMs : vld MF = true ∧ vld HM = true ∧ vld MG = true := by
  obtain ⟨a, b⟩ := andOf (a := vld MF) (b := bAnd(vld HM, vld MG)) vM
  exact ⟨a, andOf (a := vld HM) (b := vld MG) b⟩

theorem hm_eq : r3eHM (U B4) = U HM := by
  unfold r3eHM
  rw [matA_eq, matB_eq, mulE vA vB, mulE (mulV vA vB) vA, mulE vB4 vA,
    mulE (mulV (mulV vA vB) vA) (mulV vB4 vA), Nat.eq_of_beq_eq_true hm]

theorem mg_eq : r3eGM (U HM) (U MF) = U MG := by
  obtain ⟨vf, vh, _⟩ := vMs
  unfold r3eGM
  rw [mulE vh vf, matA_eq, mulE vA vh, (powM_eq consts (hv (mulV vh vf)) 7).1,
    (powM_eq consts (hv (mulV vA vh)) 4).1,
    mulE (powM_eq consts (hv (mulV vh vf)) 7).2 (powM_eq consts (hv (mulV vA vh)) 4).2]
  exact congrArg (unpackL 111 12 1332) (Nat.eq_of_beq_eq_true mg)

theorem word_checks : bsWordChecks (fun i => U (TSx i)) (fun i => U (TISx i)) (U MF) (U MG) =
    true := by
  obtain ⟨vf, _, vg⟩ := vMs
  have hTs := word_of (g := fun i => U (TSx i)) (gi := fun i => U (TISx i)) (fun _ => rfl)
    (fun _ => rfl) vTSx vTISx
  have hsI : ∀ i, bsSwI i = nIf(Nat.beq i 6, 7, nIf(Nat.beq i 7, 6, i)) := fun i => by
    unfold bsSwI
    by_cases h6 : i = 6
    · subst h6
      rfl
    · by_cases h7 : i = 7
      · subst h7
        rfl
      · simp only [h6, h7, ↓reduceIte]
        rw [Bool.eq_false_iff.mpr fun h' => h6 (Nat.eq_of_beq_eq_true h'),
          Bool.eq_false_iff.mpr fun h' => h7 (Nat.eq_of_beq_eq_true h')]
  have hsw : ∀ i, U (TSx (bsSwI i)) = U (TSs i) ∧ U (TISx (bsSwI i)) = U (TISs i) := fun i => by
    rw [hsI i]
    exact ⟨rfl, rfl⟩
  have hTss := word_of (g := fun i => U (TSx (bsSwI i))) (gi := fun i => U (TISx (bsSwI i)))
    (fun i => (hsw i).1) (fun i => (hsw i).2) (fun i => by unfold TSs; exact vTSx _)
    (fun i => by unfold TISs; exact vTISx _)
  unfold bsWordChecks
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro i hi
    have hi' : i < 9 := List.mem_range.mp hi
    have e : TSx i = TS i := by unfold TSx; rw [bl (by omega)]
    beta_reduce
    rw [e, mulE (vTSi (by omega)) (vTSi (by omega)),
      mulE (mulV (vTSi (by omega)) (vTSi (by omega))) (vTSi (by omega)), idE,
      beqE (mulV (mulV (vTSi (by omega)) (vTSi (by omega))) (vTSi (by omega))) vOne]
    exact allN_spec cube i hi'
  · rw [(hTs bsWfN).1, beqE (hTs bsWfN).2 vf]
    exact wf
  · rw [matA_eq, mulE vg vA, mulE vf vg, beqE (mulV vg vA) (mulV vf vg)]
    exact gz
  · rw [(hTs bsWmN).1, (hTs bsVN).1, mulE (hTs bsWmN).2 vg, mulE vg (hTs bsVN).2,
      beqE (mulV (hTs bsWmN).2 vg) (mulV vg (hTs bsVN).2)]
    exact wm
  · rw [(hTss bsWmN).1, (hTs bsUN).1, mulE (hTss bsWmN).2 vg, mulE vg (hTs bsUN).2,
      beqE (mulV (hTss bsWmN).2 vg) (mulV vg (hTs bsUN).2)]
    exact ws

theorem facts : bsCertificate () = true := by
  unfold bsCertificate
  simp only []
  rw [b4_eq]
  unfold bsChecks
  simp only []
  rw [ta_eq, tia_eq, mf_eq, hm_eq, mg_eq]
  exact word_checks

end CertificateChecks.KernelSporSch.LyBSF

end
