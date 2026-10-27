module

public import Certificates.Kernel.Misc.GL52.IsoLemmas
public import CFSG.Literature.GL52LocalCheckInputs
public meta import CFSG.Literature.GL52Isos
public meta import CFSG.Literature.GL52Pass
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all CFSG.Literature.GL52Basic

public section

namespace CertificateChecks.KernelMisc.GL52L

open CFSG CFSG.Literature CFSG.Literature.GL52 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.KC.Misc.GLM

set_option maxRecDepth 100000

theorem orders_check : ordTest 31 2 (tbl glT0) = true ∧ ordTest 31 2 (tbl glU0) = true ∧
    ordTest 31 3 (tbl glTau1) = true ∧ ordTest 31 3 (tbl glTau2) = true ∧
    ordTest 31 3 (tbl glTauB) = true ∧ ordTest 31 5 (tbl glF5) = true ∧
    ordTest 31 15 (tbl glC15) = true ∧ ordTest 31 7 (tbl glS7) = true ∧
    ordTest 31 3 (tbl glFr) = true ∧ ordTest 31 31 (tbl glA) = true ∧
    ordTest 31 5 (tbl glH5) = true := by
  decide +kernel

theorem fix_check :
    fpT (tbl glT0) = 15 ∧ fpT (tbl glU0) = 7 ∧ fpT (tbl glTau1) = 1 ∧ fpT (tbl glTau2) = 7 := by
  decide +kernel

theorem comm_check : (gensE ++ gensT1 ++ gensT2).all (fun g => cmtT (tbl g) (tbl glT0)) = true ∧
    gensK1.all (fun g => cmtT (tbl g) (tbl glTau1)) = true ∧
    gensK2.all (fun g => cmtT (tbl g) (tbl glTau2)) = true ∧
    gensX.all (fun g => gensY.all fun h => cmtT (tbl g) (tbl h)) = true ∧
    cmtT (tbl glC15) (tbl glF5) = true ∧ cmtT (tbl glTau2) (tbl glTauB) = true := by
  decide +kernel

theorem conj_check :
    tblEq 31 (compT 31 (tbl glFr) (tbl glS7)) (compT 31 (tbl (glS7 * glS7)) (tbl glFr)) = true ∧
    tblEq 31 (compT 31 (tbl glH5) (tbl glA)) (compT 31 (tbl (glA * glA)) (tbl glH5)) = true ∧
    tblEq 31 (tbl glF5) (tbl (glC15 * glC15 * glC15)) = true ∧
    cmtT (tbl glFr) (tbl glS7) = false ∧ cmtT (tbl glH5) (tbl glA) = false ∧
    cmtT (tbl glA) (tbl glB) = false := by
  decide +kernel

theorem notMem_A5 : ∀ σ : alternatingGroup (Fin 5),
    tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 σ) (tbl glTau1) = false := by
  have h : (([] :: tblA5.map Prod.snd).all fun w => !(wK gensK1 w == cG glTau1)) = true := by
    quickRfl
  intro σ
  have hσ : (!(wK gensK1 (lkWord keyA5 tblA5 σ) == cG glTau1)) = true :=
    List.all_eq_true.1 h _ (lkWord_mem keyA5 tblA5 σ)
  change tblEq 31 (wT gensK1 (lkWord keyA5 tblA5 σ)) (tbl glTau1) = false
  rw [tblEq_wT_tbl]
  simpa using hσ

theorem notMem_GL3 : ∀ M : GL (Fin 3) (ZMod 2),
    tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 M) (tbl glTau2) = false := by
  have h : (([] :: tblGL3.map Prod.snd).all fun w => !(wK gensK2 w == cG glTau2)) = true := by
    quickRfl
  intro M
  have hM : (!(wK gensK2 (lkWord keyGL3 tblGL3 M) == cG glTau2)) = true :=
    List.all_eq_true.1 h _ (lkWord_mem keyGL3 tblGL3 M)
  change tblEq 31 (wT gensK2 (lkWord keyGL3 tblGL3 M)) (tbl glTau2) = false
  rw [tblEq_wT_tbl]
  simpa using hM

theorem enum_check : enumOK gensE wordsE = true ∧ keysDistinct 31 (enumTables gensE wordsE) = true ∧
    enumOK r0Gens r0Words = true ∧ keysDistinct 31 (enumTables r0Gens r0Words) = true ∧
    enumOK gensY wordsY = true ∧ keysDistinct 31 (enumTables gensY wordsY) = true := by
  have h1 : enumOK gensE wordsE = true := by quickRfl
  have h2 : nodupB ((enumTables gensE wordsE).map (key 31)) = true := by quickRfl
  have h3 : enumOK r0Gens r0Words = true := by quickRfl
  have h4 : nodupB ((enumTables r0Gens r0Words).map (key 31)) = true := by quickRfl
  have h5 : enumOK gensY wordsY = true := by quickRfl
  have h6 : nodupB ((enumTables gensY wordsY).map (key 31)) = true := by quickRfl
  exact ⟨h1, keysDistinct_of_nodupB 31 _ h2, h3, keysDistinct_of_nodupB 31 _ h4, h5,
    keysDistinct_of_nodupB 31 _ h6⟩

theorem abelian_E : wordsE.all (fun w => wordsE.all fun w' => cmtT (wT gensE w) (wT gensE w') &&
    tblEq 31 (compT 31 (wT gensE w) (wT gensE w)) (idT 31)) = true := by
  have h : (wordsE.all fun w => wordsE.all fun w' => (mmulK (wK gensE w) (wK gensE w') ==
      mmulK (wK gensE w') (wK gensE w)) && (mmulK (wK gensE w) (wK gensE w) == idK)) = true := by
    quickRfl
  simp only [cmtT_wT, sqId_wT]
  exact h

theorem abelian_R0 : r0Words.all (fun w => r0Words.all fun w' =>
    cmtT (wT r0Gens w) (wT r0Gens w') &&
      tblEq 31 (compT 31 (wT r0Gens w) (compT 31 (wT r0Gens w) (wT r0Gens w))) (idT 31)) =
    true := by
  have h : (r0Words.all fun w => r0Words.all fun w' => (mmulK (wK r0Gens w) (wK r0Gens w') ==
      mmulK (wK r0Gens w') (wK r0Gens w)) &&
        (mmulK (wK r0Gens w) (mmulK (wK r0Gens w) (wK r0Gens w)) == idK)) = true := by
    quickRfl
  simp only [cmtT_wT, cubeId_wT]
  exact h

theorem normalize_check : (gensT1 ++ gensT2).all (fun a => gensE.all fun e => wordsE.any fun w =>
      tblEq 31 (compT 31 (tbl a) (tbl e)) (compT 31 (wT gensE w) (tbl a))) = true ∧
    gensD.all (fun a => r0Gens.all fun x => r0Words.any fun w =>
      tblEq 31 (compT 31 (tbl a) (tbl x)) (compT 31 (wT r0Gens w) (tbl a))) = true := by
  decide +kernel

theorem ea_words : ∀ (c : Multiplicative (Fin 3 → ZMod 2)) (M : GL (Fin 3) (ZMod 2)),
    wordsE.all (fun w => !tblEq 31 (wT gensE w) (compT 31 (t1Table c) (t2Table M)) ||
      w.isEmpty) = true := by
  have h : (([] :: tblE8.map Prod.snd).all fun w₁ => ([] :: tblGL3.map Prod.snd).all fun w₂ =>
      wordsE.all fun w => !(wK gensE w == mmulK (wK gensT1 w₁) (wK gensT2 w₂)) || w.isEmpty) =
      true := by
    quickRfl
  intro c M
  have h₁ : (([] :: tblGL3.map Prod.snd).all fun w₂ => wordsE.all fun w =>
      !(wK gensE w == mmulK (wK gensT1 (lkWord keyVec tblE8 c)) (wK gensT2 w₂)) || w.isEmpty) =
      true :=
    List.all_eq_true.1 h _ (lkWord_mem keyVec tblE8 c)
  have h₂ : (wordsE.all fun w => !(wK gensE w == mmulK (wK gensT1 (lkWord keyVec tblE8 c))
      (wK gensT2 (lkWord keyGL3 tblGL3 M))) || w.isEmpty) = true :=
    List.all_eq_true.1 h₁ _ (lkWord_mem keyGL3 tblGL3 M)
  change wordsE.all (fun w => !tblEq 31 (wT gensE w) (compT 31 (wT gensT1 (lkWord keyVec tblE8 c))
    (wT gensT2 (lkWord keyGL3 tblGL3 M))) || w.isEmpty) = true
  simp only [tblEq_wT_comp]
  exact h₂

theorem ea_comm : ∀ (c : Multiplicative (Fin 3 → ZMod 2)) (M : GL (Fin 3) (ZMod 2)),
    gensE.all (fun e => cmtT (compT 31 (t1Table c) (t2Table M)) (tbl e)) = true →
      c = 1 ∧ M = 1 := by
  have h : (([] :: tblE8.map Prod.snd).all fun w₁ => ([] :: tblGL3.map Prod.snd).all fun w₂ =>
      !(gensE.all fun e => mmulK (mmulK (wK gensT1 w₁) (wK gensT2 w₂)) (cG e) ==
        mmulK (cG e) (mmulK (wK gensT1 w₁) (wK gensT2 w₂))) || (w₁.isEmpty && w₂.isEmpty)) =
      true := by
    quickRfl
  intro c M hc
  have h₁ : (([] :: tblGL3.map Prod.snd).all fun w₂ =>
      !(gensE.all fun e => mmulK (mmulK (wK gensT1 (lkWord keyVec tblE8 c)) (wK gensT2 w₂)) (cG e)
        == mmulK (cG e) (mmulK (wK gensT1 (lkWord keyVec tblE8 c)) (wK gensT2 w₂))) ||
        ((lkWord keyVec tblE8 c).isEmpty && w₂.isEmpty)) = true :=
    List.all_eq_true.1 h _ (lkWord_mem keyVec tblE8 c)
  have h₂ : (!(gensE.all fun e => mmulK (mmulK (wK gensT1 (lkWord keyVec tblE8 c))
      (wK gensT2 (lkWord keyGL3 tblGL3 M))) (cG e) == mmulK (cG e)
        (mmulK (wK gensT1 (lkWord keyVec tblE8 c)) (wK gensT2 (lkWord keyGL3 tblGL3 M)))) ||
      ((lkWord keyVec tblE8 c).isEmpty && (lkWord keyGL3 tblGL3 M).isEmpty)) = true :=
    List.all_eq_true.1 h₁ _ (lkWord_mem keyGL3 tblGL3 M)
  change gensE.all (fun e => cmtT (compT 31 (wT gensT1 (lkWord keyVec tblE8 c))
    (wT gensT2 (lkWord keyGL3 tblGL3 M))) (tbl e)) = true at hc
  simp only [cmtT_comp_tbl] at hc
  rw [hc] at h₂
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at h₂
  exact ⟨vec_one c h₂.1, gl3_one M h₂.2⟩

theorem xy_check : ∀ σ : Equiv.Perm (Fin 3), wordsY.all (fun w =>
    !tblEq 31 (lkTable gensX (keyPerm (n := 3)) tblS3 σ) (wT gensY w)) = true ∨ σ = 1 := by
  decide +kernel

open Certificates in
open CFSG CFSG.Literature CFSG.Literature.GL52 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native in
theorem facts2002 : (ordTest 31 2 (tbl glT0) = true ∧ ordTest 31 2 (tbl glU0) = true ∧
      ordTest 31 3 (tbl glTau1) = true ∧ ordTest 31 3 (tbl glTau2) = true ∧
      ordTest 31 3 (tbl glTauB) = true ∧ ordTest 31 5 (tbl glF5) = true ∧
      ordTest 31 15 (tbl glC15) = true ∧ ordTest 31 7 (tbl glS7) = true ∧
      ordTest 31 3 (tbl glFr) = true ∧ ordTest 31 31 (tbl glA) = true ∧
      ordTest 31 5 (tbl glH5) = true
    )
    ∧ (fpT (tbl glT0) = 15 ∧ fpT (tbl glU0) = 7 ∧ fpT (tbl glTau1) = 1 ∧ fpT (tbl glTau2) = 7)
    ∧ ((gensE ++ gensT1 ++ gensT2).all (fun g => cmtT (tbl g) (tbl glT0)) = true ∧
      gensK1.all (fun g => cmtT (tbl g) (tbl glTau1)) = true ∧
      gensK2.all (fun g => cmtT (tbl g) (tbl glTau2)) = true ∧
      gensX.all (fun g => gensY.all fun h => cmtT (tbl g) (tbl h)) = true ∧
      cmtT (tbl glC15) (tbl glF5) = true ∧ cmtT (tbl glTau2) (tbl glTauB) = true
    )
    ∧ (tblEq 31 (compT 31 (tbl glFr) (tbl glS7)) (compT 31 (tbl (glS7 * glS7)) (tbl glFr)) = true ∧
      tblEq 31 (compT 31 (tbl glH5) (tbl glA)) (compT 31 (tbl (glA * glA)) (tbl glH5)) = true ∧
      tblEq 31 (tbl glF5) (tbl (glC15 * glC15 * glC15)) = true ∧
      cmtT (tbl glFr) (tbl glS7) = false ∧ cmtT (tbl glH5) (tbl glA) = false ∧
      cmtT (tbl glA) (tbl glB) = false
    )
    ∧ ((∀ σ : alternatingGroup (Fin 5),
        tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 σ) (tbl glTau1) = false) ∧
      (∀ M : GL (Fin 3) (ZMod 2),
        tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 M) (tbl glTau2) = false)
    )
    ∧ (enumOK gensE wordsE = true ∧ keysDistinct 31 (enumTables gensE wordsE) = true ∧
      enumOK r0Gens r0Words = true ∧ keysDistinct 31 (enumTables r0Gens r0Words) = true ∧
      enumOK gensY wordsY = true ∧ keysDistinct 31 (enumTables gensY wordsY) = true
    )
    ∧ (wordsE.all (fun w => wordsE.all fun w' => cmtT (wT gensE w) (wT gensE w') &&
        tblEq 31 (compT 31 (wT gensE w) (wT gensE w)) (idT 31)) = true ∧
      r0Words.all (fun w => r0Words.all fun w' => cmtT (wT r0Gens w) (wT r0Gens w') &&
        tblEq 31 (compT 31 (wT r0Gens w) (compT 31 (wT r0Gens w) (wT r0Gens w))) (idT 31)) =
        true
    )
    ∧ ((gensT1 ++ gensT2).all (fun a => gensE.all fun e => wordsE.any fun w =>
        tblEq 31 (compT 31 (tbl a) (tbl e)) (compT 31 (wT gensE w) (tbl a))) = true ∧
      gensD.all (fun a => r0Gens.all fun x => r0Words.any fun w =>
        tblEq 31 (compT 31 (tbl a) (tbl x)) (compT 31 (wT r0Gens w) (tbl a))) = true
    )
    ∧ ((∀ (c : Multiplicative (Fin 3 → ZMod 2)) (M : GL (Fin 3) (ZMod 2)),
        wordsE.all (fun w => !tblEq 31 (wT gensE w) (compT 31 (t1Table c) (t2Table M)) ||
          w.isEmpty) = true) ∧
      (∀ (c : Multiplicative (Fin 3 → ZMod 2)) (M : GL (Fin 3) (ZMod 2)),
        gensE.all (fun e => cmtT (compT 31 (t1Table c) (t2Table M)) (tbl e)) = true →
          c = 1 ∧ M = 1)
    )
    ∧ (∀ σ : Equiv.Perm (Fin 3), wordsY.all (fun w =>
      !tblEq 31 (lkTable gensX (keyPerm (n := 3)) tblS3 σ) (wT gensY w)) = true ∨ σ = 1
    ) :=
  ⟨orders_check, fix_check, comm_check, conj_check, ⟨notMem_A5, notMem_GL3⟩, enum_check,
    ⟨abelian_E, abelian_R0⟩, normalize_check, ⟨ea_words, ea_comm⟩, xy_check⟩

end CertificateChecks.KernelMisc.GL52L

end
