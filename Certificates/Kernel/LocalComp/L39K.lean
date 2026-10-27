module

public import Certificates.Kernel.LocalComp.L39Data
public import Certificates.Kernel.LocalComp.Child3Lemmas
public import Certificates.Kernel.LocalComp.FendelBridge
public import Certificates.Data.Kernel.Co3Bfs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Data
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.FendelSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L39

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.O8 CFSG.KC.Child3
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.EvenSmallLie.Child3.SelL39
open CFSG.EvenSmallLie.Child3 CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)
open CFSG.KC.Fendel (lget_eq)
open CFSG.KC.Co3Bfs (allFrom)

theorem permLT1 : allN 7 (fun j => permOK 91 7 (mask 7) (91 * 7) (LT1.S j) (LT1.SI j)) = true := by
  quickRfl
theorem permLT : allN 7 (fun j => permOK 182 8 (mask 8) (182 * 8) (LT.S j) (LT.SI j)) = true := by
  quickRfl
theorem permLS : allN 8 (fun j => permOK 182 8 (mask 8) (182 * 8) (LS.S j) (LS.SI j)) = true := by
  quickRfl

theorem lA_eq : lA = unpack 91 7 LAP := by decide +kernel
theorem lB_eq : lB = unpack 91 7 LBP := by decide +kernel
theorem kLA : invEqK 91 7 (mask 7) (91 * 7) LAP (pinvS 91 7 (mask 7) LAP) = true := by quickRfl
theorem kLB : invEqK 91 7 (mask 7) (91 * 7) LBP (pinvS 91 7 (mask 7) LBP) = true := by quickRfl

theorem inv_of {n w P R : Nat} (h : invEqK n w (mask w) (n * w) P R = true) :
    isInvA n (unpack n w P) (invCand n (unpack n w P)) = true := by
  obtain ⟨e1, e2⟩ := invEqK_sound h
  rw [e1]
  exact e2

theorem tChain : tChainCheck = true := by
  unfold tChainCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [wordsOf_eq]
    exact rawChainK_sound (NS := 6) (CH := 16) bindsLT1 LT1.head LT1.hl (by norm_num) LT1.hs
  · change rawOrbitSizes 91 t1S t1BaseArr = _
    rw [rawOrbitSizesK_sound bindsLT1 permLT1 LT1.hl]
    decide
  · rw [wordsOf_eq]
    exact rawChainK_sound (NS := 12) (CH := 16) bindsLT LT.head LT.hl (by norm_num) LT.hs
  · change rawOrbitSizes 182 tS tBaseArr = _
    rw [rawOrbitSizesK_sound bindsLT permLT LT.hl]
    decide
  · rw [lA_eq]
    exact inv_of kLA
  · rw [lB_eq]
    exact inv_of kLB

theorem autChain : autChainCheck = true := by
  unfold autChainCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · rw [wordsOf_eq]
    exact rawChainK_sound (NS := 12) (CH := 16) bindsLA LA.head LA.hl (by norm_num) LA.hs
  · change rawOrbitSizes 182 autS autBaseArr = _
    rw [rawOrbitSizesK_sound bindsLA permLA LA.hl]
    decide

theorem sylowChain : sylowChainCheck = true := by
  unfold sylowChainCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [bindsLA.2.2.2.1]
    decide
  · rw [wordsOf_eq]
    exact rawChainK_sound (NS := 12) (CH := 16) bindsLS LS.head LS.hl (by norm_num) LS.hs
  · change rawOrbitSizes 182 sylowS sylowBaseArr = _
    rw [rawOrbitSizesK_sound bindsLS permLS LS.hl]
    decide

theorem kCanA : allN 15 (fun j => bAnd(canonK 182 8 (mask 8) (182 * 8) (LA.S j),
    canonK 182 8 (mask 8) (182 * 8) (LA.SI j))) = true := by quickRfl

theorem kCanT : allN 7 (fun j => canonK 182 8 (mask 8) (182 * 8) (LT.S j)) = true := by quickRfl

theorem cLA (j : Nat) (hj : j < 15) : CnN 182 8 (LA.S j) ∧ CnN 182 8 (LA.SI j) :=
  (bAnd_iff _ _).1 (allN_spec kCanA j hj)

theorem cLT (j : Nat) (hj : j < 7) : CnN 182 8 (LT.S j) := allN_spec kCanT j hj

@[expose] noncomputable def normK (i k : Nat) : Bool :=
  strictB (pcomp 182 8 (mask 8) (pcomp 182 8 (mask 8) (LA.S (2 + i)) (LT.S k)) (LA.SI (2 + i)))
    (fun X => bAnd(Nat.beq (Nat.shiftRight X (182 * 8)) 0,
      siftK 182 8 (mask 8) (182 * 8) (pidn 182 8) LT.LR LT.TRI LT.BP 5 0 X))

theorem kNorm : allN 2 (fun i => allN 2 (fun k => normK i k)) = true := by quickRfl

theorem norm1 (i k : Nat) (hi : i < 2) (hk : k < 2) :
    siftA 182 (rawLevels 182 tS (tBase.map Fin.val).toArray) (tBase.map Fin.val).toArray 0
      (conjA 182 (unpack 182 8 (LA.S (2 + i))) (unpack 182 8 (LT.S k))) = true := by
  have h := allN_spec (allN_spec kNorm i hi) k hk
  unfold normK at h
  rw [CFSG.KC.Fendel.strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨cg, cgi⟩ := cLA (2 + i) (by omega)
  have ck := cLT k (by omega)
  have e : conjA 182 (unpack 182 8 (LA.S (2 + i))) (unpack 182 8 (LT.S k)) =
      unpack 182 8 (pcomp 182 8 (mask 8) (pcomp 182 8 (mask 8) (LA.S (2 + i)) (LT.S k))
        (LA.SI (2 + i))) := by
    unfold conjA
    rw [(invEqK_sound (allN_spec permLA (2 + i) (by omega))).1, compA_unpackN cg ck,
      compA_unpackN (canon_pcN cg ck) cgi]
  rw [e]
  exact siftK_soundR bindsLT permLT LT.hl rfl (Nat.eq_of_beq_eq_true h1)
    (range_of_canonK (canon_pcN (canon_pcN cg ck) cgi)) h2

theorem normC : normCheck = true := by
  unfold normCheck
  have hs : sig182 = unpack 182 8 (LA.S 2) := a_2
  have hg : gam182 = unpack 182 8 (LA.S 3) := a_3
  have hqa : qA = unpack 182 8 (LT.S 0) := t_0
  have hqb : qB = unpack 182 8 (LT.S 1) := t_1
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [hs, hg, hqa, hqb]
  exact ⟨⟨inv_of (allN_spec permLA 2 (by omega)), norm1 0 0 (by omega) (by omega),
      norm1 0 1 (by omega) (by omega)⟩,
    ⟨inv_of (allN_spec permLA 3 (by omega)), norm1 1 0 (by omega) (by omega),
      norm1 1 1 (by omega) (by omega)⟩⟩

theorem kStab : l39Roots.all (fun r => stabK 182 8 LT.S LT.SI 7 r.1 r.2) = true := by quickRfl

theorem kForest : forestK 182 8 LT.S 7 (l39Roots.map Prod.fst) LF.FP LF.FL LF.FD = true := by
  quickRfl

theorem kRootsND : CFSG.KC.Misc.Oq.nodupK (l39Roots.map Prod.fst) = true := by quickRfl

theorem centC : centCheck = true :=
  centOK_sound (by quickRfl) kRootsND ⟨bindsLT.2.2.2.1, bindsLT.2.2.2.2.1⟩ permLT kStab kForest

theorem kRep : allN 11 (fun i => wordEqK 182 8 (mask 8) (pidn 182 8) LS.S LS.SI 8
    (repWords.getD i []) (LR.E (lget LR.OFF i))) = true := by quickRfl

theorem repWords_length : repWords.length = 11 := rfl

theorem rep_get (i : Nat) (hi : i < 11) :
    repArrs[i]'(by simp [repArrs, repWords_length, hi]) =
      unpack 182 8 (LR.E (lget LR.OFF i)) := by
  have h := (wordEqK_sound (S := sylowS) ⟨bindsLS.2.2.2.1, bindsLS.2.2.2.2.1⟩ permLS
    (allN_spec kRep i hi)).1
  simp only [repArrs, List.getElem_map, sylowW]
  rw [← h, List.getD_eq_getElem _ _ (by rw [repWords_length]; exact hi)]

theorem reps_eq : repArrs = (List.range 11).map fun i => unpack 182 8 (LR.E (lget LR.OFF i)) := by
  apply List.ext_getElem
  · simp [repArrs, repWords_length]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact rep_get i (by simpa using h2)

theorem kInv : Nat.beq (invCount2 182 8 LS.LR LS.TR) 119 = true := by quickRfl

theorem kOff : offOK LR.CS LR.OFF 119 = true := by quickRfl

theorem kPos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) LR.CS = true := by quickRfl

theorem kR0 : allFrom 0 60 (repK 182 8 LS.S LS.SI 4 LR.CS LR.OFF LR.CI LR.E LR.P LR.L LR.K
    LR.S LR.SI 119 100) = true := by quickRfl
theorem kR1 : allFrom 60 59 (repK 182 8 LS.S LS.SI 4 LR.CS LR.OFF LR.CI LR.E LR.P LR.L LR.K
    LR.S LR.SI 119 100) = true := by quickRfl

theorem rep_all (j : Nat) (hj : j < 119) : repK 182 8 LS.S LS.SI 4 LR.CS LR.OFF LR.CI LR.E LR.P
    LR.L LR.K LR.S LR.SI 119 100 j = true := by
  by_cases h : j < 60
  · have := allN_spec kR0 j h
    rw [CFSG.KC.Fendel.strictB_eq] at this
    simpa using this
  · have := allN_spec kR1 (j - 60) (by omega)
    rw [CFSG.KC.Fendel.strictB_eq] at this
    have e : Nat.add 60 (j - 60) = j := Nat.add_sub_cancel' (by omega)
    rwa [e] at this

theorem kCanS : allN 4 (fun j => bAnd(canonK 182 8 (mask 8) (182 * 8) (LS.S j),
    canonK 182 8 (mask 8) (182 * 8) (LS.SI j))) = true := by quickRfl

theorem kOrdK : allN 11 (fun i => bAnd(canonK 182 8 (mask 8) (182 * 8) (LR.E (lget LR.OFF i)),
    Nat.beq (pcomp 182 8 (mask 8) (LR.E (lget LR.OFF i)) (LR.E (lget LR.OFF i))) (pidn 182 8) &&
      !Nat.beq (LR.E (lget LR.OFF i)) (pidn 182 8))) = true := by quickRfl

theorem kOrd : ((List.range 11).map fun i => unpack 182 8 (LR.E (lget LR.OFF i))).all
    (fun r => ordTest 182 2 (arrTable 182 r)) = true := by
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
  obtain ⟨c, h⟩ := (bAnd_iff _ _).1 (allN_spec kOrdK i (List.mem_range.1 hi))
  rw [ordTest2_unpack c]
  exact h

theorem repsC : repsCheck = true := by
  unfold repsCheck
  rw [Bool.and_eq_true]
  refine ⟨?_, by rw [reps_eq]; exact kOrd⟩
  have hsg : sylowGens.size = 4 := sg_orig.1
  refine repsOK_sound (g := 4) (N := 119) ⟨by simp [sylowGensT, hsg],
    by simp [sylowGensInvT, hsg], fun l hl => ⟨?_, ?_⟩⟩
    (fun l hl => (bAnd_iff _ _).1 (allN_spec kCanS l hl)) ?_ kOff kPos ?_ rep_all
  · unfold sylowGensT
    rw [getElem!_map' (by rw [hsg]; exact hl), sg_orig.2 l hl]
  · unfold sylowGensInvT
    rw [getElem!_map' (by rw [hsg]; exact hl), sg_orig.2 l hl,
      (invEqK_sound (allN_spec permLS l (by omega))).1]
  · rw [reps_eq, List.map_map]
    rfl
  · unfold invList sylowTables
    exact (invList2_sound bindsLS permLS LS.hl).trans (Nat.eq_of_beq_eq_true kInv)

theorem kWit : allN 11 (fun j => wordEqK 182 8 (mask 8) (pidn 182 8) LT.S LT.SI 7
    (witWords.getD j []) (wv 182 8 LT.S LT.SI (witWords.getD j []))) = true := by quickRfl

@[expose] noncomputable def witK (j : Nat) : Bool :=
  strictB (wv 182 8 LT.S LT.SI (witWords.getD j [])) (fun W => strictB (LR.E (lget LR.OFF j))
    (fun Y => bAnd(canonK 182 8 (mask 8) (182 * 8) W, bAnd(canonK 182 8 (mask 8) (182 * 8) Y,
    bAnd(Nat.beq (pcomp 182 8 (mask 8) W Y) (pcomp 182 8 (mask 8) Y W),
    bAnd(bIf(Nat.beq (ppowN 182 8 W 4) (pidn 182 8), false, true),
    bAnd(bIf(Nat.beq (ppowN 182 8 W 6) (pidn 182 8), false, true),
      bIf(Nat.beq (ppowN 182 8 W 14) (pidn 182 8), false, true))))))))

theorem kWitK : allN 11 witK = true := by quickRfl

theorem kId : idK 182 8 (mask 8) = true := by quickRfl
theorem kIdc : CnN 182 8 (pidn 182 8) := by quickRfl

theorem witC : witCheck = true := by
  unfold witCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, rfl⟩, rfl⟩, ?_⟩
  · rw [bindsLS.2.2.2.1]
    decide
  · rw [bindsLT.2.2.2.1]
    decide
  · rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    have hid := idK_sound kId
    have hw := (wordEqK_sound (S := tS) ⟨bindsLT.2.2.2.1, bindsLT.2.2.2.2.1⟩ permLT
      (allN_spec kWit j hj')).1
    have h := allN_spec kWitK j hj'
    unfold witK at h
    rw [CFSG.KC.Fendel.strictB_eq, CFSG.KC.Fendel.strictB_eq] at h
    obtain ⟨cw, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨cy, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h6, h14⟩ := (bAnd_iff _ _).1 h
    have hy : repArrs.getD j #[] = unpack 182 8 (LR.E (lget LR.OFF j)) := by
      rw [List.getD_eq_getElem _ _ (by simp [repArrs, repWords_length]; exact hj'), rep_get j hj']
    unfold witOK tW
    rw [hy, hw, compA_unpackN cw cy, compA_unpackN cy cw,
      eqA_unpackN (canon_pcN cw cy) (canon_pcN cy cw), (powN_unpack cw hid kIdc 4).1,
      (powN_unpack cw hid kIdc 6).1, (powN_unpack cw hid kIdc 14).1, ← hid,
      eqA_unpackN (powN_unpack cw hid kIdc 4).2 kIdc, eqA_unpackN (powN_unpack cw hid kIdc 6).2 kIdc,
      eqA_unpackN (powN_unpack cw hid kIdc 14).2 kIdc, h1]
    revert h4 h6 h14
    cases Nat.beq (ppowN 182 8 (wv 182 8 LT.S LT.SI (witWords.getD j [])) 4) (pidn 182 8) <;>
      cases Nat.beq (ppowN 182 8 (wv 182 8 LT.S LT.SI (witWords.getD j [])) 6) (pidn 182 8) <;>
      cases Nat.beq (ppowN 182 8 (wv 182 8 LT.S LT.SI (witWords.getD j [])) 14) (pidn 182 8) <;>
      simp

theorem facts3965 : (tChainCheck = true) ∧ (autChainCheck = true) ∧ (sylowChainCheck = true) ∧
    (normCheck = true) ∧ (centCheck = true) ∧ (repsCheck = true) ∧ (witCheck = true) :=
  ⟨tChain, autChain, sylowChain, normC, centC, repsC, witC⟩

end CertificateChecks.KernelLC.L39

end
