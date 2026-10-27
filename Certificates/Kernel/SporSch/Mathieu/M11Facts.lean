module

public import Certificates.Kernel.SporSch.Mathieu.M11Data
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M11OC

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC

theorem bindA : bindListK 11 4 (M11Q.S 0) tA = true := by quickRfl

theorem bindB : bindListK 11 4 (M11Q.S 1) tB = true := by quickRfl

theorem pA : permOK 11 4 (mask 4) (11 * 4) (M11Q.S 0) (M11Q.SI 0) = true := by quickRfl

theorem pB : permOK 11 4 (mask 4) (11 * 4) (M11Q.S 1) (M11Q.SI 1) = true := by quickRfl

theorem cA : canonK 11 4 (mask 4) (11 * 4) (M11Q.S 0) = true := by quickRfl

theorem cB : canonK 11 4 (mask 4) (11 * 4) (M11Q.S 1) = true := by quickRfl

theorem cOne : canonK 11 4 (mask 4) (11 * 4) One = true := by quickRfl

theorem gensC1a : allN 4 (fun j => abOK (m11CentWords1.getD j [])) = true := by quickRfl

theorem gensC1b : allN 4 (fun j => Nat.beq (abWordK 11 4 (mask 4) (pidn 11 4) (M11Q.S 0)
    (M11Q.SI 0) (M11Q.S 1) (M11Q.SI 1) (m11CentWords1.getD j [])) (M11C1.S j)) = true := by
  quickRfl

theorem repOK1 : abOK (m11InvRepWords.getD 0 []) = true := by quickRfl

theorem repOK2 : Nat.beq (abWordK 11 4 (mask 4) (pidn 11 4) (M11Q.S 0) (M11Q.SI 0) (M11Q.S 1)
    (M11Q.SI 1) (m11InvRepWords.getD 0 [])) R0 = true := by quickRfl

theorem commC1 : allN 4 (fun j => commK 11 4 (mask 4) (11 * 4) (M11C1.S j) R0) = true := by
  quickRfl

theorem ordA : ordIs 11 4 (mask 4) (pidn 11 4) (M11Q.S 0) (2 - 1) = true := by quickRfl

theorem ordB : ordIs 11 4 (mask 4) (pidn 11 4) (M11Q.S 1) (4 - 1) = true := by quickRfl

theorem wordsAB : wordOrdK 11 4 (mask 4) (pidn 11 4) 2 4 m11AutWords (M11Q.S 0) (M11Q.S 1) =
    true := by quickRfl

theorem clsOK' : allC (clsOneR 11 4 tA tB 2 400) M11CL = true := by quickRfl

theorem disjOK : clsDisj 11 4 M11CL = true := by quickRfl

theorem neOK : allC (fun d => Nat.blt 0 (CFSG.KS.Mathieu.lenN d.2.2.2.2.2.2)) M11CL = true := by
  quickRfl

theorem emptyCls : allC (clsOneR 11 4 tA tB 2 400)
      [(0, 0, (M11CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1,
        [(M11CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1], [], [], [])] = true ∧
    clsDisj 11 4 [(0, 0, (M11CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1,
        [(M11CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1], [], [], [])] = true ∧
    (allC (fun d => Nat.blt 0 (CFSG.KS.Mathieu.lenN d.2.2.2.2.2.2))
      [(0, 0, (M11CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1,
        [(M11CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1], [], [], [])]).not = true := by
  refine ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem szOK' : szOK 11 4 = true := by quickRfl

theorem tA_eq : tA = imageList m11gA := by decide

theorem tB_eq : tB = imageList m11gB := by decide

theorem img_of_bind {g : Equiv.Perm (Fin 11)} {l : List Nat} {P : Nat} (hl : l = imageList g)
    (h : bindListK 11 4 P l = true) : imageList g = (unpack 11 4 P).toList := by
  rw [← hl, ← toArray_eq_of_bindListK h]

theorem imgA : imageList m11gA = (unpack 11 4 (M11Q.S 0)).toList := img_of_bind tA_eq bindA

theorem imgB : imageList m11gB = (unpack 11 4 (M11Q.S 1)).toList := img_of_bind tB_eq bindB

theorem getD_map_eval (ws : List (List Int)) (S : List (Equiv.Perm (Fin 11))) (j : Nat) :
    (ws.map (evalCodes S)).getD j 1 = evalCodes S (ws.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> rfl

theorem img_word {wd : List Int} {P : Nat} (hw : abOK wd = true)
    (h : Nat.beq (abWordK 11 4 (mask 4) (pidn 11 4) (M11Q.S 0) (M11Q.SI 0) (M11Q.S 1) (M11Q.SI 1)
      wd) P = true) :
    imageList (evalCodes [m11gA, m11gB] wd) = (unpack 11 4 P).toList := by
  rw [abWordK_rep szOK' imgA imgB pA pB hw, Nat.eq_of_beq_eq_true h]

theorem imgOne : imageList (1 : Equiv.Perm (Fin 11)) = (unpack 11 4 One).toList := by
  decide

theorem imgRep : imageList (m11InvReps.getD 0 1) = (unpack 11 4 R0).toList := by
  rw [m11InvReps, getD_map_eval]
  exact img_word repOK1 repOK2

theorem chainQ : ChainK 11 4 [m11gA, m11gB] m11Words (#v[0, 1, 2, 3] : Vector (Fin 11) 4)
    M11Q.S M11Q.SI M11Q.LR M11Q.TR M11Q.TRI 6 M11Q.BP 1 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M11Q.head, M11Q.hl,
    by norm_num, M11Q.hs⟩
  have hj2 : j < 2 := hj
  interval_cases j
  · exact imgA
  · exact imgB

theorem chainC1 : ChainK 11 4 (m11CentWords1.map (evalCodes [m11gA, m11gB])) m11CentChainWords1
    (#v[0, 1, 2] : Vector (Fin 11) 3) M11C1.S M11C1.SI M11C1.LR M11C1.TR M11C1.TRI 8 M11C1.BP 1 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M11C1.head, M11C1.hl,
    by norm_num, M11C1.hs⟩
  have hj4 : j < 4 := by simpa [m11CentWords1] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensC1a j hj4) (allN_spec gensC1b j hj4)

theorem cosetX : (cosetOrderTables m11Certificate 1 2).length = M11X.CS.sum :=
  chainK_cosetCount (by decide) (by decide) chainQ imgOne cOne (by norm_num) (by norm_num) (by decide) M11X.hc

theorem hR : m11InvReps.length = M11CL.length ∧ ∀ j < M11CL.length,
    imageList (m11InvReps.getD j 1) =
      (unpack 11 4 (M11CL.getD j (0, 0, 0, [], [], [], [])).2.2.1).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj1 : j < 1 := by simpa [M11CL] using hj
  interval_cases j
  exact imgRep

theorem cover : repsOK 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
        (cosetOrderTables m11Certificate 1 2) (m11InvReps.map toTable) 400 = true ∧
      repSizes 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
        (m11InvReps.map toTable) 400 = [165] ∧
      (m11InvReps.map toTable).all (ordTest 11 2) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps tA_eq tB_eq szOK' clsOK' disjOK hR (by norm_num)
    (X := cosetOrderTables m11Certificate 1 2) (by rw [cosetX]; decide) neOK (by norm_num)
  exact ⟨h1, h2.trans (by decide), h3⟩

theorem cent1 : m11CentQ1.check = true ∧ m11CentQ1.orderCertificate = 48 ∧
      (m11CentWords1.map (evalCodes [m11gA, m11gB])).all
        (fun h => commT 11 (toTable h) (toTable ((m11InvReps).getD 0 1))) = true ∧
      oddWitnessOK 11 3 (allTables m11CentQ1) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainC1
  refine ⟨h1, h2.trans (by decide), ?_, chainK_odd (by decide) (by decide) chainC1 M11O.ok⟩
  rw [List.all_eq_true]
  intro h hh
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hh
  have hj4 : j < 4 := by simpa [m11CentWords1] using hj
  have himg := chainC1.2.2.2.1 j hj
  rw [List.getD_eq_getElem _ _ hj] at himg
  exact commT_of_commK himg imgRep (allN_spec commC1 j hj4)

theorem aut : ordTest 11 2 (toTable m11gA) = true ∧ ordTest 11 4 (toTable m11gB) = true ∧
      wordsTest 11 2 4 m11AutWords (toTable m11gA) (toTable m11gB) = true ∧
      repsTotal 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
        (m11InvReps.map toTable) (orderTables m11Certificate 4) 400
        (wordsTest 11 2 4 m11AutWords) = 7920 := by
  refine ⟨ordTest_of_ordIs szOK' imgA cA (by norm_num) ordA,
    ordTest_of_ordIs szOK' imgB cB (by norm_num) ordB,
    wordsTest_of_wordOrdK szOK' imgA imgB wordsAB, ?_⟩
  have h := chainK_repsTotal (mx := 2) (my := 4) (by decide) (by decide) chainQ tA_eq tB_eq
    (by norm_num) clsOK' hR (by norm_num) (by norm_num) (CW := [M11Y.CS])
    ⟨rfl, fun j hj => by
      have hj1 : j < 1 := by simpa [M11CL] using hj
      interval_cases j
      exact ⟨by decide, M11Y.hc⟩⟩ neOK
  exact h.trans (by decide)

theorem facts : (repsOK 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
        (cosetOrderTables m11Certificate 1 2) (m11InvReps.map toTable) 400 = true ∧
      repSizes 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
        (m11InvReps.map toTable) 400 = [165] ∧
      (m11InvReps.map toTable).all (ordTest 11 2) = true
    )
    ∧ (m11CentQ1.check = true ∧ m11CentQ1.orderCertificate = 48 ∧
      (m11CentWords1.map (evalCodes [m11gA, m11gB])).all
        (fun h => commT 11 (toTable h) (toTable ((m11InvReps).getD 0 1))) = true ∧
      oddWitnessOK 11 3 (allTables m11CentQ1) = true
    )
    ∧ (ordTest 11 2 (toTable m11gA) = true ∧ ordTest 11 4 (toTable m11gB) = true ∧
      wordsTest 11 2 4 m11AutWords (toTable m11gA) (toTable m11gB) = true ∧
      repsTotal 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
        (m11InvReps.map toTable) (orderTables m11Certificate 4) 400 (wordsTest 11 2 4 m11AutWords) =
          7920
    ) := ⟨cover, cent1, aut⟩

end CertificateChecks.KernelSporSch.M11OC

end
