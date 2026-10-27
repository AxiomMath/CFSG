
module

public import Certificates.Kernel.SporSch.J4S.FiveW
public import CFSG.Certificates.Kernel.SporSch.J4SSylowSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch
open scoped Matrix

theorem e0 : Nat.beq pidK (J4E.T 0) = true := by quickRfl

theorem eltP : allN 1024 (fun e => bIf(Nat.beq e 0, true,
    bAnd(Nat.blt (ent 10 (J4D.T e) 0) e, bAnd(Nat.blt (ent 10 (J4D.T e) 1) 4,
      Nat.beq (compK (J4E.T (ent 10 (J4D.T e) 0)) (J4GC (ent 10 (J4D.T e) 1))) (J4E.T e))))) =
    true := by quickRfl

theorem eltR : allN 1024 (fun e => allN 4 (fun i => bAnd(Nat.blt (ent 10 (J4R.T e) i) 1024,
    Nat.beq (compK (J4E.T e) (J4GC i)) (J4E.T (ent 10 (J4R.T e) i))))) = true := by quickRfl

theorem dist : distinctK J4E.T J4ES.SO J4ES.SOI 1024 = true := by quickRfl

theorem ct0 : Nat.beq (J4CT.T 0) 0 = true := by quickRfl

theorem ct : allN 1024 (fun e => bAnd(Nat.blt (J4CT.T e) 16, allN 4 (fun i =>
    Nat.beq (J4CT.T (ent 10 (J4R.T e) i)) (Nat.xor (J4CT.T e) (Nat.pow 2 i))))) = true := by
  quickRfl

theorem sq : allN 1024 (fun e => bAnd(Nat.blt (J4SQ.T e) 1024,
    Nat.beq (compK (J4E.T e) (J4E.T e)) (J4E.T (J4SQ.T e)))) = true := by quickRfl

theorem ellc : allN 1024 (fun e => allN 11 (fun j =>
    Nat.beq (ellK (ent 11 (J4E.T e) j)) (ellK (Nat.pow 2 j)))) = true := by quickRfl

theorem vec : allN 1024 (fun e => vecK 300 (J4E.T e)) = true := by quickRfl

theorem span : allN 11 (fun j => Nat.beq (appK (J4E.T j) 4) (ent 11 J4NB j)) = true := by quickRfl

theorem inj : injK J4NB = true := by quickRfl

theorem beq_ne {k : Nat} (h : 0 < k) : Nat.beq k 0 = false :=
  Bool.eq_false_iff.2 fun e => by have := Nat.eq_of_beq_eq_true e; omega

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem span_get {j : Nat} (hj : j < 11) :
    spanIdx[j]! < 1024 ∧ app11 elementColumns[spanIdx[j]!]! 4 = normalOrbitSpanBasis.toArray[j]! := by
  have hsz : normalOrbitSpanBasis.toArray.size = 11 := rfl
  have hj' : j < (normalOrbitSpanBasis.toArray.map fun b =>
      ((List.range 1024).find? fun e => app11 elementColumns[e]! 4 == b).getD 0).size := by
    rw [Array.size_map, hsz]
    exact hj
  have e1 : spanIdx[j]! = ((List.range 1024).find? fun e =>
      app11 elementColumns[e]! 4 == normalOrbitSpanBasis.toArray[j]!).getD 0 := by
    rw [spanIdx, getElem!_pos _ j hj', Array.getElem_map,
      ← getElem!_pos normalOrbitSpanBasis.toArray j (by rw [hsz]; exact hj)]
  have hw : app11 elementColumns[j]! 4 = normalOrbitSpanBasis.toArray[j]! := by
    rw [E_eq (by omega), app_eq, NB_get hj]
    exact Nat.eq_of_beq_eq_true (allN_spec span j hj)
  rw [e1]
  cases hx : (List.range 1024).find? fun e =>
      app11 elementColumns[e]! 4 == normalOrbitSpanBasis.toArray[j]! with
  | none =>
    have := List.find?_eq_none.1 hx j (List.mem_range.2 (by omega))
    simp [hw] at this
  | some x =>
    rw [Option.getD_some]
    have hp := List.find?_some hx
    exact ⟨List.mem_range.1 (List.mem_of_find?_eq_some hx), beq_iff_eq.1 hp⟩

theorem facts : (∀ i < 4, wordCols (fiveGenWords[i]!) = generatorColumns[i]!) ∧
    (∀ i < 4, (generatorColumns[i]!).size = 11 ∧ ∀ j < 11, (generatorColumns[i]!)[j]! < 2048) ∧
    (elementColumns.size = 1024) ∧ (elementColumns[0]! = idRows 11) ∧
    (∀ e < 1024, (elementColumns[e]!).size = 11 ∧ (∀ j < 11, (elementColumns[e]!)[j]! < 2048) ∧
      (0 < e → (discoveryParents[e]!)[0]! < e ∧ (discoveryParents[e]!)[1]! < 4 ∧
        elementColumns[e]! = comp11 elementColumns[(discoveryParents[e]!)[0]!]!
          generatorColumns[(discoveryParents[e]!)[1]!]!) ∧
      ∀ i < 4, (rightEdges[e]!)[i]! < 1024 ∧
        elementColumns[(rightEdges[e]!)[i]!]! = comp11 elementColumns[e]! generatorColumns[i]!) ∧
    (∀ e < 1024, ∀ e' < e, elementColumns[e']! ≠ elementColumns[e]!) ∧
    (cTable[0]! = 0) ∧
    (∀ e < 1024, cTable[e]! < 16 ∧ ∀ i < 4, cTable[(rightEdges[e]!)[i]!]! = cTable[e]! ^^^ 2 ^ i) ∧
    (∀ e < 1024, squares[e]! < 1024 ∧
      elementColumns[squares[e]!]! = comp11 elementColumns[e]! elementColumns[e]!) ∧
    (∀ e < 1024, ∀ j < 11, ell ((elementColumns[e]!)[j]!) = ell (2 ^ j)) ∧
    (∀ e < 1024, CFSG.Sporadic.SmallF2.toVecD 11 300 ᵥ* colsMatrix (elementColumns[e]!) =
      CFSG.Sporadic.SmallF2.toVecD 11 300) ∧
    (∀ j < 11, spanIdx[j]! < 1024 ∧
      app11 elementColumns[spanIdx[j]!]! 4 = normalOrbitSpanBasis.toArray[j]!) ∧
    (∀ c < 2048, ∀ c' < c,
      app11 normalOrbitSpanBasis.toArray c' ≠ app11 normalOrbitSpanBasis.toArray c) ∧
    (normalOrbitSpanBasis.toArray.size = 11 ∧ ∀ j < 11, normalOrbitSpanBasis.toArray[j]! < 2048) := by
  have hNB : normalOrbitSpanBasis.toArray = unpack11 J4NB := bindW_sound nb
  refine ⟨gens_eq, fun i hi => ?_, E_size, ?_, fun e he => ?_, fun e he e' he' => ?_, ?_,
    fun e he => ?_, fun e he => ?_, fun e he j hj => ?_, fun e he => ?_, fun j hj => span_get hj,
    ?_, ?_⟩
  · rw [GC_eq hi]
    exact unpack11_bounded _
  · rw [E_eq (by omega), CFSG.KS.SporSch.C11.id_eq]
    exact congrArg unpack11 (Nat.eq_of_beq_eq_true e0)
  · rw [E_eq he]
    refine ⟨(unpack11_bounded _).1, (unpack11_bounded _).2, fun he0 => ?_, fun i hi => ?_⟩
    · have h := allN_spec eltP e he
      rw [beq_ne he0] at h
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
      obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
      have l1 := lt_of_blt h1
      have l2 := lt_of_blt h3
      rw [D_get he (by omega), D_get he (by omega), E_eq (by omega), GC_eq l2, comp_eq]
      exact ⟨l1, l2, (congrArg unpack11 (Nat.eq_of_beq_eq_true h4)).symm⟩
    · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec eltR e he) i hi)
      have l1 := lt_of_blt h1
      rw [R_get he hi, E_eq l1, GC_eq hi, comp_eq]
      exact ⟨l1, (congrArg unpack11 (Nat.eq_of_beq_eq_true h2)).symm⟩
  · rw [E_eq (by omega), E_eq he]
    exact distinctK_sound dist e he e' he'
  · rw [CT_eq, tabA_get (by omega)]
    exact Nat.eq_of_beq_eq_true ct0
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec ct e he)
    rw [CT_eq, tabA_get he]
    refine ⟨lt_of_blt h1, fun i hi => ?_⟩
    have hr := allN_spec (allN_spec eltR e he) i hi
    have lr := lt_of_blt ((bAnd_iff _ _).1 hr).1
    rw [R_get he hi, tabA_get lr]
    exact Nat.eq_of_beq_eq_true (allN_spec h2 i hi)
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec sq e he)
    have l1 := lt_of_blt h1
    rw [SQ_eq, tabA_get he, E_eq l1, E_eq he, comp_eq]
    exact ⟨l1, (congrArg unpack11 (Nat.eq_of_beq_eq_true h2)).symm⟩
  · rw [E_eq he, unpack11, unpackW_get hj]
    exact ellK_sound (allN_spec (allN_spec ellc e he) j hj)
  · rw [E_eq he]
    exact vecK_sound (by decide) (allN_spec vec e he)
  · rw [hNB]
    exact injK_sound inj
  · rw [hNB]
    exact unpack11_bounded _

end CertificateChecks.KernelSporSch.J4Five

end
