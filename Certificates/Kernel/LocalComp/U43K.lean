module

public import Certificates.Kernel.LocalComp.U43Data
public import Certificates.Kernel.LocalComp.L39K
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Data
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.U43

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.O8 CFSG.KC.Child3
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.EvenSmallLie.Child3.SelU43
open CFSG.EvenSmallLie.Child3 CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover CFSG.LieType.Multipliers.U43
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)
open CFSG.KC.Fendel (lget_eq)
open CFSG.KC.Co3Bfs (allFrom)
open CertificateChecks.KernelLC.L39 (inv_of)
open CertificateChecks.KernelU43B (C.S C.SI C.LR C.TR C.TRI C.BP C.hl C.head C.hs)

theorem tChain : tChainCheck = true := by
  unfold tChainCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨CertificateChecks.KernelU43B.chain_check, ?_⟩
  rw [CertificateChecks.KernelU43B.base_eq,
    rawOrbitSizesK_sound CertificateChecks.KernelU43B.binds CertificateChecks.KernelU43B.perm C.hl]
  decide

theorem autChain : autChainCheck = true := by
  unfold autChainCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · rw [wordsOf_eq]
    exact rawChainK_sound (NS := 13) (CH := 64) bindsUA UA.head UA.hl (by norm_num) UA.hs
  · change rawOrbitSizes 820 autS autBaseArr = _
    rw [rawOrbitSizesK_sound bindsUA permUA UA.hl]
    decide

theorem sylowChain : sylowChainCheck = true := by
  unfold sylowChainCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [bindsUA.2.2.2.1]
    decide
  · rw [wordsOf_eq]
    exact rawChainK_sound (NS := 13) (CH := 64) bindsUS US.head US.hl (by norm_num) US.hs
  · change rawOrbitSizes 820 sylowS sylowBaseArr = _
    rw [rawOrbitSizesK_sound bindsUS permUS US.hl]
    decide

theorem kCanA : allN 10 (fun j => bAnd(canonK 820 10 (mask 10) (820 * 10) (UA.S j),
    canonK 820 10 (mask 10) (820 * 10) (UA.SI j))) = true := by quickRfl

theorem kCanT : allN 7 (fun j => canonK 820 10 (mask 10) (820 * 10) (C.S j)) = true := by quickRfl

theorem cUA (j : Nat) (hj : j < 10) : CnN 820 10 (UA.S j) ∧ CnN 820 10 (UA.SI j) :=
  (bAnd_iff _ _).1 (allN_spec kCanA j hj)

theorem cT (j : Nat) (hj : j < 7) : CnN 820 10 (C.S j) := allN_spec kCanT j hj

@[expose] noncomputable def normK (i k : Nat) : Bool :=
  strictB (pcomp 820 10 (mask 10) (pcomp 820 10 (mask 10) (UA.S (2 + i)) (C.S k)) (UA.SI (2 + i)))
    (fun X => bAnd(Nat.beq (Nat.shiftRight X (820 * 10)) 0,
      siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0 X))

theorem kNorm : allN 2 (fun i => allN 2 (fun k => normK i k)) = true := by quickRfl

theorem norm1 (i k : Nat) (hi : i < 2) (hk : k < 2) :
    siftA 820 (rawLevels 820 chainS (chainBase.map Fin.val).toArray) (chainBase.map Fin.val).toArray 0
      (conjA 820 (unpack 820 10 (UA.S (2 + i))) (unpack 820 10 (C.S k))) = true := by
  have h := allN_spec (allN_spec kNorm i hi) k hk
  unfold normK at h
  rw [CFSG.KC.Fendel.strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨cg, cgi⟩ := cUA (2 + i) (by omega)
  have ck := cT k (by omega)
  have e : conjA 820 (unpack 820 10 (UA.S (2 + i))) (unpack 820 10 (C.S k)) =
      unpack 820 10 (pcomp 820 10 (mask 10) (pcomp 820 10 (mask 10) (UA.S (2 + i)) (C.S k))
        (UA.SI (2 + i))) := by
    unfold conjA
    rw [(invEqK_sound (allN_spec permUA (2 + i) (by omega))).1, compA_unpackN cg ck,
      compA_unpackN (canon_pcN cg ck) cgi]
  rw [e, CertificateChecks.KernelU43B.base_eq]
  exact siftK_soundR CertificateChecks.KernelU43B.binds CertificateChecks.KernelU43B.perm C.hl rfl
    (Nat.eq_of_beq_eq_true h1) (range_of_canonK (canon_pcN (canon_pcN cg ck) cgi)) h2

theorem normC : normCheck = true := by
  unfold normCheck
  have hd : deltaArr = unpack 820 10 (UA.S 2) := a_2
  have hs : sigmaArr = unpack 820 10 (UA.S 3) := a_3
  have ha : tabA = unpack 820 10 (C.S 0) := CertificateChecks.KernelU43B.binds.2.2.2.2.1 0 (by omega)
  have hb : tabB = unpack 820 10 (C.S 1) := CertificateChecks.KernelU43B.binds.2.2.2.2.1 1 (by omega)
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [hd, hs, ha, hb]
  exact ⟨⟨inv_of (allN_spec permUA 2 (by omega)), norm1 0 0 (by omega) (by omega),
      norm1 0 1 (by omega) (by omega)⟩,
    ⟨inv_of (allN_spec permUA 3 (by omega)), norm1 1 0 (by omega) (by omega),
      norm1 1 1 (by omega) (by omega)⟩⟩

theorem kStab : u43Roots.all (fun r => stabK 820 10 C.S C.SI 7 r.1 r.2) = true := by quickRfl

theorem kForest : forestK 820 10 C.S 7 (u43Roots.map Prod.fst) UF.FP UF.FL UF.FD = true := by
  quickRfl

theorem kRootsND : CFSG.KC.Misc.Oq.nodupK (u43Roots.map Prod.fst) = true := by quickRfl

theorem centC : centCheck = true :=
  centOK_sound (by quickRfl) kRootsND
    ⟨CertificateChecks.KernelU43B.binds.2.2.2.1, CertificateChecks.KernelU43B.binds.2.2.2.2.1⟩
    CertificateChecks.KernelU43B.perm kStab kForest

theorem kRep : allN 19 (fun i => wordEqK 820 10 (mask 10) (pidn 820 10) US.S US.SI 6
    (repWords.getD i []) (UR.E (lget UR.OFF i))) = true := by quickRfl

theorem repWords_length : repWords.length = 19 := rfl

theorem rep_get (i : Nat) (hi : i < 19) :
    repArrs[i]'(by simp [repArrs, repWords_length, hi]) =
      unpack 820 10 (UR.E (lget UR.OFF i)) := by
  have h := (wordEqK_sound (S := sylowS) ⟨bindsUS.2.2.2.1, bindsUS.2.2.2.2.1⟩ permUS
    (allN_spec kRep i hi)).1
  simp only [repArrs, List.getElem_map, sylowW]
  rw [← h, List.getD_eq_getElem _ _ (by rw [repWords_length]; exact hi)]

theorem reps_eq : repArrs = (List.range 19).map fun i => unpack 820 10 (UR.E (lget UR.OFF i)) := by
  apply List.ext_getElem
  · simp [repArrs, repWords_length]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact rep_get i (by simpa using h2)


theorem hInv : invCount2 820 10 US.LR US.TR = 191 := by decide +kernel

theorem kOff : offOK UR.CS UR.OFF 191 = true := by quickRfl

theorem kPos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) UR.CS = true := by quickRfl

theorem kR0 : allFrom 0 48 (repK 820 10 US.S US.SI 4 UR.CS UR.OFF UR.CI UR.E UR.P UR.L UR.K
    UR.S UR.SI 191 100) = true := by quickRfl
theorem kR1 : allFrom 48 48 (repK 820 10 US.S US.SI 4 UR.CS UR.OFF UR.CI UR.E UR.P UR.L UR.K
    UR.S UR.SI 191 100) = true := by quickRfl
theorem kR2 : allFrom 96 48 (repK 820 10 US.S US.SI 4 UR.CS UR.OFF UR.CI UR.E UR.P UR.L UR.K
    UR.S UR.SI 191 100) = true := by quickRfl
theorem kR3 : allFrom 144 47 (repK 820 10 US.S US.SI 4 UR.CS UR.OFF UR.CI UR.E UR.P UR.L UR.K
    UR.S UR.SI 191 100) = true := by quickRfl

theorem from_block {f : Nat → Bool} {a len j : Nat} (h : allFrom a len f = true) (h1 : a ≤ j)
    (h2 : j < a + len) : f j = true := by
  have := allN_spec h (j - a) (by omega)
  rw [CFSG.KC.Fendel.strictB_eq] at this
  have e : Nat.add a (j - a) = j := Nat.add_sub_cancel' h1
  rwa [e] at this

theorem rep_all (j : Nat) (hj : j < 191) : repK 820 10 US.S US.SI 4 UR.CS UR.OFF UR.CI UR.E UR.P
    UR.L UR.K UR.S UR.SI 191 100 j = true := by
  by_cases h0 : j < 48
  · exact from_block kR0 (by omega) (by omega)
  by_cases h1 : j < 96
  · exact from_block kR1 (by omega) (by omega)
  by_cases h2 : j < 144
  · exact from_block kR2 (by omega) (by omega)
  · exact from_block kR3 (by omega) (by omega)

theorem kCanS : allN 4 (fun j => bAnd(canonK 820 10 (mask 10) (820 * 10) (US.S j),
    canonK 820 10 (mask 10) (820 * 10) (US.SI j))) = true := by quickRfl

theorem kOrdK : allN 19 (fun i => bAnd(canonK 820 10 (mask 10) (820 * 10) (UR.E (lget UR.OFF i)),
    Nat.beq (pcomp 820 10 (mask 10) (UR.E (lget UR.OFF i)) (UR.E (lget UR.OFF i))) (pidn 820 10) &&
      !Nat.beq (UR.E (lget UR.OFF i)) (pidn 820 10))) = true := by quickRfl

theorem kOrd : ((List.range 19).map fun i => unpack 820 10 (UR.E (lget UR.OFF i))).all
    (fun r => ordTest 820 2 (arrTable 820 r)) = true := by
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
  refine repsOK_sound (g := 4) (N := 191) ⟨by simp [sylowGensT, hsg],
    by simp [sylowGensInvT, hsg], fun l hl => ⟨?_, ?_⟩⟩
    (fun l hl => (bAnd_iff _ _).1 (allN_spec kCanS l hl)) ?_ kOff kPos ?_ rep_all
  · unfold sylowGensT
    rw [getElem!_map' (by rw [hsg]; exact hl), sg_orig.2 l hl]
  · unfold sylowGensInvT
    rw [getElem!_map' (by rw [hsg]; exact hl), sg_orig.2 l hl,
      (invEqK_sound (allN_spec permUS l (by omega))).1]
  · rw [reps_eq, List.map_map]
    rfl
  · have e : (sylowBase.map Fin.val).toArray = sylowBaseArr := rfl
    unfold invList sylowTables
    have h := invList2_sound bindsUS permUS US.hl
    rw [← e] at h
    exact h.trans hInv

theorem kWit : allN 19 (fun j => wordEqK 820 10 (mask 10) (pidn 820 10) C.S C.SI 7
    (witWords.getD j []) (wv 820 10 C.S C.SI (witWords.getD j []))) = true := by quickRfl

@[expose] noncomputable def witK (j : Nat) : Bool :=
  strictB (wv 820 10 C.S C.SI (witWords.getD j [])) (fun W => strictB (UR.E (lget UR.OFF j))
    (fun Y => bAnd(canonK 820 10 (mask 10) (820 * 10) W, bAnd(canonK 820 10 (mask 10) (820 * 10) Y,
    bAnd(Nat.beq (pcomp 820 10 (mask 10) W Y) (pcomp 820 10 (mask 10) Y W),
    bAnd(bIf(Nat.beq (ppowN 820 10 W 4) (pidn 820 10), false, true),
    bAnd(bIf(Nat.beq (ppowN 820 10 W 6) (pidn 820 10), false, true),
      bIf(Nat.beq (ppowN 820 10 W 14) (pidn 820 10), false, true))))))))

theorem kWitK0 : allFrom 0 10 witK = true := by quickRfl
theorem kWitK1 : allFrom 10 9 witK = true := by quickRfl

theorem kId : idK 820 10 (mask 10) = true := by quickRfl
theorem kIdc : CnN 820 10 (pidn 820 10) := by quickRfl

theorem witC : witCheck = true := by
  unfold witCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, rfl⟩, rfl⟩, ?_⟩
  · rw [bindsUS.2.2.2.1]
    decide
  · rw [CertificateChecks.KernelU43B.binds.2.2.2.1]
    decide
  · rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    have hid := idK_sound kId
    have hw := (wordEqK_sound (S := chainS) ⟨CertificateChecks.KernelU43B.binds.2.2.2.1,
      CertificateChecks.KernelU43B.binds.2.2.2.2.1⟩ CertificateChecks.KernelU43B.perm
      (allN_spec kWit j hj')).1
    have h : witK j = true := by
      by_cases hl : j < 10
      · exact from_block kWitK0 (by omega) (by omega)
      · exact from_block kWitK1 (by omega) (by omega)
    unfold witK at h
    rw [CFSG.KC.Fendel.strictB_eq, CFSG.KC.Fendel.strictB_eq] at h
    obtain ⟨cw, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨cy, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h6, h14⟩ := (bAnd_iff _ _).1 h
    have hy : repArrs.getD j #[] = unpack 820 10 (UR.E (lget UR.OFF j)) := by
      rw [List.getD_eq_getElem _ _ (by simp [repArrs, repWords_length]; exact hj'), rep_get j hj']
    unfold witOK tW
    rw [hy, hw, compA_unpackN cw cy, compA_unpackN cy cw,
      eqA_unpackN (canon_pcN cw cy) (canon_pcN cy cw), (powN_unpack cw hid kIdc 4).1,
      (powN_unpack cw hid kIdc 6).1, (powN_unpack cw hid kIdc 14).1, ← hid,
      eqA_unpackN (powN_unpack cw hid kIdc 4).2 kIdc, eqA_unpackN (powN_unpack cw hid kIdc 6).2 kIdc,
      eqA_unpackN (powN_unpack cw hid kIdc 14).2 kIdc, h1]
    revert h4 h6 h14
    cases Nat.beq (ppowN 820 10 (wv 820 10 C.S C.SI (witWords.getD j [])) 4) (pidn 820 10) <;>
      cases Nat.beq (ppowN 820 10 (wv 820 10 C.S C.SI (witWords.getD j [])) 6) (pidn 820 10) <;>
      cases Nat.beq (ppowN 820 10 (wv 820 10 C.S C.SI (witWords.getD j [])) 14) (pidn 820 10) <;>
      simp

theorem facts3964 : (tChainCheck = true) ∧ (autChainCheck = true) ∧ (sylowChainCheck = true) ∧
    (normCheck = true) ∧ (centCheck = true) ∧ (repsCheck = true) ∧ (witCheck = true) :=
  ⟨tChain, autChain, sylowChain, normC, centC, repsC, witC⟩

end CertificateChecks.KernelLC.U43

end
