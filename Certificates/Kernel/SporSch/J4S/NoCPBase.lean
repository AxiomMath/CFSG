
module

public import Certificates.Kernel.SporSch.J4S.NoCK
public import Certificates.Kernel.SporSch.J4S.Form
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.J4SBfsProved
import Mathlib.Tactic.IntervalCases

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4NoCP

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta
open CertificateChecks.KernelSporSch.J4NoCK CertificateChecks.KernelSporSch.J4InvP

theorem anyK_eq (f : Nat → Bool) : ∀ n, J4InvC.anyK n f = (List.range n).any f
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.any_append, ← anyK_eq f n]
    change Bool.rec (motive := fun _ => Bool) (J4InvC.anyK n f) true (f n) = _
    cases hf : f n <;> simp [hf]

theorem memL_iff {x : Nat} : ∀ {l : List Nat}, memL x l = true ↔ x ∈ l
  | [] => by simp [memL]
  | y :: l => by
    change Bool.rec (motive := fun _ => Bool) (memL x l) true (Nat.beq x y) = true ↔ _
    by_cases h : x = y
    · rw [beq_iff.2 h]
      simp [h]
    · rw [beqF h, memL_iff]
      simp [h]

theorem allL_iff {f : Nat → Bool} : ∀ {l : List Nat}, allL l f = true ↔ ∀ x ∈ l, f x = true
  | [] => by simp [allL]
  | y :: l => by
    change Bool.rec (motive := fun _ => Bool) false (allL l f) (f y) = true ↔ _
    rw [bAnd_iff, allL_iff]
    simp

theorem cntK_eq (f : Nat → Bool) :
    ∀ n, cntK n f = ((Finset.range n).filter fun k => f k = true).card
  | 0 => rfl
  | n + 1 => by
    change cntK n f + Bool.rec (motive := fun _ => Nat) 0 1 (f n) = _
    rw [cntK_eq f n, Finset.range_add_one, Finset.filter_insert]
    cases hf : f n
    · simp
    · rw [ite_eq_left rfl, Finset.card_insert_of_notMem (by simp)]

theorem recAll {P : Nat × Nat × List Int → Bool} : ∀ {L : List (Nat × Nat × List Int)},
    List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec (motive := fun _ => Bool) false
      ih (P e)) L = true → ∀ e ∈ L, P e = true
  | [], _, e, he => absurd he (List.not_mem_nil)
  | x :: L, h, e, he => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rcases List.mem_cons.1 he with rfl | he
    · exact h1
    · exact recAll h2 e he

theorem getL_eq : ∀ (L : List (List Nat)) (i : Nat), L[i]?.getD [] = getL L i
  | [], i => by cases i <;> rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by
    rw [List.getElem?_cons_succ]
    exact getL_eq L i

theorem dSets_get (l : Nat) : dSets[l]! = getL dSets.toList l := by
  rw [← getL_eq, getElem!_def, Array.getElem?_toList]
  cases dSets[l]? <;> rfl

theorem cb_get : ∀ j < 7, getN 0 chainBase.toList j = chainBase[j]! := by decide +kernel

theorem unMats_get {j : Nat} (hj : j < 11) : unMats[j]! = (Un ⟨j, hj⟩).1 := by
  rw [unMats, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem etaN_eq (s a : Nat) : ∀ n ≤ 11, (List.range n).foldl
    (fun acc j => if a.testBit j then O.vmul acc unMats[j]! else acc) s = etaN n s a
  | 0, _ => rfl
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      etaN_eq s a n (by omega)]
    change _ = CFSG.KC.Loop.strictN (etaN n s a) fun x =>
      Bool.rec (motive := fun _ => Nat) x (vecJ rm x (E (Nat.add 13 n))) (Nat.testBit a n)
    rw [strictN_eq']
    have hv : O.vmul (etaN n s a) unMats[n]! = vecJ rm (etaN n s a) (E (Nat.add 13 n)) := by
      rw [unMats_get (by omega)]
      have p := pU ⟨n, by omega⟩
      change vecMulN 112 _ _ = _
      rw [vec_enc J4Real.hK p.1.1, p.1.2]
      rfl
    cases h : a.testBit n
    · rfl
    · rw [ite_eq_left rfl, hv]

theorem etaV_eq (s a : Nat) : NoComp.etaV unMats s a = J4NoCK.etaK s a := by
  unfold NoComp.etaV J4NoCK.etaK
  have e : (List.finRange 11).map Fin.val = List.range 11 := by decide
  rw [← etaN_eq s a 11 le_rfl, ← e, List.foldl_map]

theorem vne_eq (x y : Nat) : O.vne x y = vneK x y := by
  rw [vneK, anyK_eq]
  rfl

theorem pRep {l : Nat} (hl : l < 7) :
    PairOK (repPair l) (getN one J4RP l) (getN one J4RP (7 + l)) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec rp l hl)
  have hlet : ∀ x ∈ repWords[l]!, x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 := by
    interval_cases l <;> decide
  have pw := wordP_ok' J4Real.hK pA pB _ hlet
  have e : J4InvA.getW repWords.toList l = repWords[l]! := by
    rw [← J4InvP.getW_eq, getElem!_def, Array.getElem?_toList]
    cases repWords[l]? <;> rfl
  refine ofEq pw ?_ ?_
  · rw [← beq_iff.1 h1, RF, e]
  · have h2' : RS l = getN one J4RP (7 + l) := beq_iff.1 h2
    rw [← h2', RS, e]

theorem rv_get {l : Nat} (hl : l < 7) : repVecs[l]! = J4RV l := by
  rw [repVecs, getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  change O.vmul rootBits (repPair l).1 = J4RV l
  have ev : O.vmul rootBits (repPair l).1 = vecMulN 112 (repPair l).1 rootBits := rfl
  rw [ev]
  have p := pRep hl
  rw [vec_enc J4Real.hK p.1.1, p.1.2]
  exact beq_iff.1 (allN_spec rv l hl)

theorem cj_ok {l j : Nat} (hl : l < 7) (hj : j < 11) :
    WfN (NoComp.conjTab[l]!)[j]! ∧ encN (NoComp.conjTab[l]!)[j]! = getN one J4CJ (11 * l + j) := by
  have e : (NoComp.conjTab[l]!)[j]! = (conjPair l ⟨j, hj⟩).1 := by
    rw [NoComp.conjTab, getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn,
      getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  have p := mulP_ok J4Real.hK (mulP_ok J4Real.hK (invP_ok (pRep hl)) (pU ⟨j, hj⟩)) (pRep hl)
  rw [e]
  refine ⟨p.1.1, p.1.2.trans ?_⟩
  have h := beq_iff.1 (allN_spec cj (11 * l + j) (by omega))
  have d1 : Nat.div (11 * l + j) 11 = l := by
    change (11 * l + j) / 11 = l
    omega
  have d2 : Nat.mod (11 * l + j) 11 = j := by
    change (11 * l + j) % 11 = j
    omega
  rw [d1, d2] at h
  rw [h]
  rfl

theorem letter_eq (l : Int) (b : Nat) : letterApp l b = letK J4X J4XI J4Y J4YI l b := by
  have hx : xColumns = unpack11 J4X := bindW_sound J4X.bind
  have hxi : xInvColumns = unpack11 J4XI := bindW_sound J4XI.bind
  have hy : yColumns = unpack11 J4Y := bindW_sound J4Y.bind
  have hyi : yInvColumns = unpack11 J4YI := bindW_sound J4YI.bind
  unfold letterApp
  split_ifs with h1 h2 h3 h4
  · subst h1
    rw [hx, app_eq]
    rfl
  · subst h2
    rw [hxi, app_eq]
    rfl
  · subst h3
    rw [hy, app_eq]
    rfl
  · subst h4
    rw [hyi, app_eq]
    rfl
  · rcases l with k | k
    · have k1 : k ≠ 1 := fun e => h1 (by rw [e]; rfl)
      have k2 : k ≠ 2 := fun e => h3 (by rw [e]; rfl)
      change b = Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) b (appK J4Y b) (Nat.beq k 2)) (appK J4X b) (Nat.beq k 1)
      rw [beqF k1, beqF k2]
    · have k0 : k ≠ 0 := fun e => h2 (by rw [e]; rfl)
      have k1 : k ≠ 1 := fun e => h4 (by rw [e]; rfl)
      change b = Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) b (appK J4YI b) (Nat.beq k 1)) (appK J4XI b)
        (Nat.beq k 0)
      rw [beqF k0, beqF k1]

theorem app11W_eq : ∀ (w : List Int) (a : Nat), app11W w a = wordAppK J4X J4XI J4Y J4YI w a
  | [], _ => rfl
  | l :: w, a => by
    rw [app11W, app11W_eq w a, letter_eq]
    exact (strictN_eq' _ _).symm

theorem sTab_get {i : Nat} (hi : i < 8) : sTab[i]! = unpack11 (J4G1 i) := by
  rw [← J4Orbits.g1_bind.2 i hi]
  interval_cases i <;> rfl

theorem swApp_eq : ∀ (w : List Nat), w.all (· < 8) = true → ∀ a, swApp sTab w a = swK w a
  | [], _, _ => rfl
  | i :: w, h, a => by
    rw [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    change app11 sTab[i]! (swApp sTab w a) = CFSG.KC.Loop.strictN (swK w a) fun b => appK (J4G1 i) b
    rw [swApp_eq w h.2 a, strictN_eq', sTab_get h.1, app_eq]

@[expose] def chainP (F : List Nat → Nat → Nat) : Prop :=
  ∀ j ∈ [1, 2, 3, 4, 5, 6], (chainWords[j - 1]!).size = chainCnt[j]! ∧
    ∀ k < chainCnt[j]!, ((chainWords[j - 1]!)[k]!).all (· < 8) = true ∧
      (∀ i < j, F (chainWords[j - 1]!)[k]! chainBase[i]! = chainBase[i]!) ∧
      F (chainWords[j - 1]!)[k]! chainBase[j]! < 2048 ∧
      ∀ k' < chainCnt[j]!, F (chainWords[j - 1]!)[k]! chainBase[j]! =
        F (chainWords[j - 1]!)[k']! chainBase[j]! → k = k'

theorem chainK : chainP swK := by
  unfold chainP
  decide +kernel

theorem chain_ok : chainP (swApp sTab) := by
  intro j hj
  obtain ⟨h1, h2⟩ := chainK j hj
  refine ⟨h1, fun k hk => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h2 k hk
  refine ⟨a1, fun i hi => ?_, ?_, fun k' hk' e => a4 k' hk' ?_⟩
  · rw [swApp_eq _ a1]
    exact a2 i hi
  · rw [swApp_eq _ a1]
    exact a3
  · rw [swApp_eq _ a1, swApp_eq _ (h2 k' hk').1] at e
    exact e

theorem fix_ok {l : Nat} (hl : l < 7) :
    ((Finset.range 2048).filter fun a => NoComp.etaV unMats repVecs[l]! a = repVecs[l]!).card =
        repCounts[l]! ∧
      ∀ a < 2048, NoComp.etaV unMats repVecs[l]! a = repVecs[l]! ∨
        O.vne (NoComp.etaV unMats repVecs[l]! a) repVecs[l]! = true := by
  rw [rv_get hl]
  refine ⟨?_, fun a ha => ?_⟩
  · have e : ((Finset.range 2048).filter fun a => NoComp.etaV unMats (J4RV l) a = J4RV l) =
        (Finset.range 2048).filter fun a => Nat.beq (J4NoCK.etaK (J4RV l) a) (J4RV l) = true := by
      apply Finset.filter_congr
      intro a _
      rw [etaV_eq, beq_iff]
    rw [e, ← cntK_eq]
    interval_cases l
    · exact beq_iff.1 cnt0
    · exact beq_iff.1 cnt1
    · exact beq_iff.1 cnt2
    · exact beq_iff.1 cnt3
    · exact beq_iff.1 cnt4
    · exact beq_iff.1 cnt5
    · exact beq_iff.1 cnt6
  · have h := allN_spec (allN_spec nes l hl) a ha
    rw [etaV_eq, vne_eq]
    by_cases e : J4NoCK.etaK (J4RV l) a = J4RV l
    · exact Or.inl e
    · rw [bIf_f (beqF e)] at h
      exact Or.inr h

theorem bil_ok {w : Nat} {b : Bool} (h : bilK w b = true) : bilB rootBits w = b := by
  unfold bilK at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  have hc := ofFn_enc J4Real.hK (f := fun i : Fin 112 => if w.testBit i then 1 else 0)
    (fun i => by split_ifs <;> norm_num) h1 (fun i => by
      rw [beq_iff.1 (allN_spec h2 i i.isLt)]
      cases w.testBit i <;> rfl)
  unfold bilB
  change (vecMulN 112 (colRows w) (vecMulN 112 formRows rootBits)).testBit 0 = b
  rw [vec_enc J4Real.hK J4Form.hR.1, J4Form.hR.2]
  unfold colRows
  rw [vec_enc J4Real.hK hc.1, hc.2]
  cases ht : Nat.testBit (vecJ rm (vecJ rm rootBits J4FR) (CP w)) 0 <;> cases b <;>
    simp_all [notB]

theorem outside_ok : outsideOK unMats NoComp.conjTab = true := by
  unfold outsideOK
  rw [List.all_eq_true]
  intro l hl
  rw [List.mem_range'_1] at hl
  rw [List.all_eq_true]
  intro a ha
  rw [List.mem_range'_1] at ha
  have hk := slice_spec (k := 256) (S := 48) (by omega) J4NO.all (2048 * (l - 1) + a) (by omega)
  unfold outI at hk
  rw [bIf_t (blt_iff.2 (by omega))] at hk
  have d1 : Nat.succ (Nat.div (2048 * (l - 1) + a) 2048) = l := by
    change (2048 * (l - 1) + a) / 2048 + 1 = l
    omega
  have d2 : Nat.mod (2048 * (l - 1) + a) 2048 = a := by
    change (2048 * (l - 1) + a) % 2048 = a
    omega
  rw [d1, d2] at hk
  unfold outK at hk
  rw [bIf_f (beqF (by omega : a ≠ 0))] at hk
  rw [Bool.or_eq_true]
  by_cases hm : memL a (getL dSets.toList l) = true
  · left
    rw [List.contains_iff_mem, dSets_get]
    exact memL_iff.1 hm
  · right
    rw [Bool.not_eq_true] at hm
    rw [hm] at hk
    simp only [J4InvP.strictB_eq] at hk
    obtain ⟨w1, hk⟩ := (bAnd_iff _ _).1 hk
    obtain ⟨w2, hk⟩ := (bAnd_iff _ _).1 hk
    have hj := blt_iff.1 w2
    set w := ent 11 (J4OW l) a
    have hc := cj_ok (by omega : l < 7) hj
    rw [List.any_eq_true]
    refine ⟨Nat.div (Nat.sub w 1) 112, List.mem_range.2 hj, ?_⟩
    unfold ncommE
    rw [List.any_eq_true]
    refine ⟨Nat.mod (Nat.sub w 1) 112, List.mem_range.2 (Nat.mod_lt _ (by omega)), ?_⟩
    rw [vne_eq]
    change vneK (vecMulN 112 _ (NoComp.etaV unMats (1 <<< _) a))
      (NoComp.etaV unMats (vecMulN 112 _ (1 <<< _)) a) = true
    rw [vec_enc J4Real.hK hc.1, vec_enc J4Real.hK hc.1, hc.2, etaV_eq, etaV_eq]
    exact hk

end CertificateChecks.KernelSporSch.J4NoCP

end
