module

public import Certificates.Kernel.SporSch.Mathieu.M22OX
public import Certificates.Kernel.SporSch.Mathieu.M22Facts
public import CFSG.Certificates.Kernel.SporSch.MathieuClsSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22OC

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC

theorem bindD : bindListK 22 5 M22D tD = true := by quickRfl

theorem pD : permOK 22 5 (mask 5) (22 * 5) M22D (pinvS 22 5 (mask 5) M22D) = true := by quickRfl

theorem cD : canonK 22 5 (mask 5) (22 * 5) M22D = true := by quickRfl

@[expose] noncomputable def CA : Nat :=
  pcomp 22 5 (mask 5) (pcomp 22 5 (mask 5) M22D (M22Q.S 0)) (pinvS 22 5 (mask 5) M22D)

@[expose] noncomputable def CB : Nat :=
  pcomp 22 5 (mask 5) (pcomp 22 5 (mask 5) M22D (M22Q.S 1)) (pinvS 22 5 (mask 5) M22D)

theorem cCA : canonK 22 5 (mask 5) (22 * 5) CA = true := by quickRfl

theorem cCB : canonK 22 5 (mask 5) (22 * 5) CB = true := by quickRfl

theorem siftCA : siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) M22Q.LR M22Q.TRI M22Q.BP 5 0 CA = true := by
  quickRfl

theorem siftCB : siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) M22Q.LR M22Q.TRI M22Q.BP 5 0 CB = true := by
  quickRfl

theorem gensO1a : allN 3 (fun j => abOK (m22OutCentWords1.getD j [])) = true := by quickRfl

theorem gensO1b : allN 3 (fun j => Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0)
    (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) (m22OutCentWords1.getD j [])) (M22OC1.S j)) = true := by
  quickRfl

theorem gensO2a : allN 3 (fun j => abOK (m22OutCentWords2.getD j [])) = true := by quickRfl

theorem gensO2b : allN 3 (fun j => Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0)
    (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) (m22OutCentWords2.getD j [])) (M22OC2.S j)) = true := by
  quickRfl

theorem orep0a : abOK (m22OutRepWords.getD 0 []) = true := by quickRfl

theorem orep0b : Nat.beq (pcomp 22 5 (mask 5) (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0)
    (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) (m22OutRepWords.getD 0 [])) M22D) RO0 = true := by quickRfl

theorem orep1a : abOK (m22OutRepWords.getD 1 []) = true := by quickRfl

theorem orep1b : Nat.beq (pcomp 22 5 (mask 5) (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0)
    (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) (m22OutRepWords.getD 1 [])) M22D) RO1 = true := by quickRfl

theorem commO1 : allN 3 (fun j => commK 22 5 (mask 5) (22 * 5) (M22OC1.S j) RO0) = true := by
  quickRfl

theorem commO2 : allN 3 (fun j => commK 22 5 (mask 5) (22 * 5) (M22OC2.S j) RO1) = true := by
  quickRfl


theorem tD_eq : tD = imageList m22Delta := by decide

theorem imgD : imageList m22Delta = (unpack 22 5 M22D).toList := img_of_bind tD_eq bindD

theorem imgDi : imageList m22Delta⁻¹ = (unpack 22 5 (pinvS 22 5 (mask 5) M22D)).toList :=
  invK_rep imgD pD

theorem imgCA : imageList (m22Delta * m22gA * m22Delta⁻¹) = (unpack 22 5 CA).toList := by
  rw [mulK_rep szOK' (mulK_rep szOK' imgD imgA) imgDi]
  rfl

theorem imgCB : imageList (m22Delta * m22gB * m22Delta⁻¹) = (unpack 22 5 CB).toList := by
  rw [mulK_rep szOK' (mulK_rep szOK' imgD imgB) imgDi]
  rfl

theorem imgRO (j : Nat) (hj : j < 2) {R : Nat} (ha : abOK (m22OutRepWords.getD j []) = true)
    (hb : Nat.beq (pcomp 22 5 (mask 5) (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0)
      (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) (m22OutRepWords.getD j [])) M22D) R = true) :
    imageList (m22OutReps.getD j 1) = (unpack 22 5 R).toList := by
  have hl : j < m22OutRepWords.length := by simpa [m22OutRepWords] using hj
  rw [m22OutReps, List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
    mulK_rep szOK' (abWordK_rep szOK' imgA imgB pA pB
      (by rw [List.getD_eq_getElem _ _ hl] at ha; exact ha)) imgD,
    ← Nat.eq_of_beq_eq_true hb, List.getD_eq_getElem _ _ hl]

theorem imgRO0 : imageList (m22OutReps.getD 0 1) = (unpack 22 5 RO0).toList :=
  imgRO 0 (by norm_num) orep0a orep0b

theorem imgRO1 : imageList (m22OutReps.getD 1 1) = (unpack 22 5 RO1).toList :=
  imgRO 1 (by norm_num) orep1a orep1b

theorem oclsOK : ClsOK 22 5 tA tB 2 2000 M22OCL := by
  intro j hj
  have hj2 : j < 2 := by simpa [M22OCL] using hj
  interval_cases j
  · exact ⟨M22OCL.h0, elems_of_blocks (by decide) M22OCL.hb0, fun i hi => absurd hi (by omega)⟩
  · refine ⟨M22OCL.h1, elems_of_blocks (by decide) M22OCL.hb1, fun i hi => ?_⟩
    have hi0 : i = 0 := by omega
    subst hi0
    exact M22OCL.n1_0

theorem chainO1 : ChainK 22 5 (m22OutCentWords1.map (evalCodes [m22gA, m22gB]))
    m22OutCentChainWords1 (#v[0, 1, 2] : Vector (Fin 22) 3) M22OC1.S M22OC1.SI M22OC1.LR
    M22OC1.TR M22OC1.TRI 8 M22OC1.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M22OC1.head,
    M22OC1.hl, by norm_num, M22OC1.hs⟩
  have hj3 : j < 3 := by simpa [m22OutCentWords1] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensO1a j hj3) (allN_spec gensO1b j hj3)

theorem chainO2 : ChainK 22 5 (m22OutCentWords2.map (evalCodes [m22gA, m22gB]))
    m22OutCentChainWords2 (#v[0, 1, 2] : Vector (Fin 22) 3) M22OC2.S M22OC2.SI M22OC2.LR
    M22OC2.TR M22OC2.TRI 8 M22OC2.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M22OC2.head,
    M22OC2.hl, by norm_num, M22OC2.hs⟩
  have hj3 : j < 3 := by simpa [m22OutCentWords2] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensO2a j hj3) (allN_spec gensO2b j hj3)

theorem delta : m22Delta * m22Delta = 1 ∧ m22Certificate.sift (m22Delta * m22gA * m22Delta⁻¹) 0 = true ∧
      m22Certificate.sift (m22Delta * m22gB * m22Delta⁻¹) 0 = true ∧
      countProducts 22 (commAll 22 [toTable m22gA, toTable m22gB]) (levelTables m22Certificate)
        (toTable m22Delta) = 0 := by
  refine ⟨by decide, chainK_sift (by decide) (by decide) chainQ imgCA cCA siftCA,
    chainK_sift (by decide) (by decide) chainQ imgCB cCB siftCB, ?_⟩
  exact (chainK_commCount (by decide) (by decide) chainQ imgD cD imgA cA imgB cB (by norm_num)
    M22OZ.hc).trans (by decide)

theorem hRO : m22OutReps.length = M22OCL.length ∧ ∀ j < M22OCL.length,
    imageList (m22OutReps.getD j 1) = (unpack 22 5 (M22OCL.getD j clsD0).R).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj2 : j < 2 := by simpa [M22OCL] using hj
  interval_cases j
  · exact imgRO0
  · exact imgRO1

theorem cosetOX : (cosetOrderTables m22Certificate m22Delta 2).length =
    (M22OX.CS.map List.sum).sum :=
  chainK_cosetCount2 (by decide) (by decide) chainQ imgD cD (by norm_num) (by norm_num) M22OX.hc

theorem ocover : repsOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (cosetOrderTables m22Certificate m22Delta 2) (m22OutReps.map toTable) 2000 = true ∧
      repSizes 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (m22OutReps.map toTable) 2000 = [1386, 330] ∧
      (m22OutReps.map toTable).all (ordTest 22 2) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps3 tA_eq tB_eq szOK' oclsOK hRO (by norm_num)
    (X := cosetOrderTables m22Certificate m22Delta 2) (by rw [cosetOX]; decide)
  exact ⟨h1, h2.trans (by decide), h3⟩

theorem ocent1 : m22OutCentQ1.check = true ∧ m22OutCentQ1.orderCertificate = 320 ∧
      (m22OutCentWords1.map (evalCodes [m22gA, m22gB])).all
        (fun h => commT 22 (toTable h) (toTable (m22OutReps.getD 0 1))) = true ∧
      oddWitnessOK 22 5 (allTables m22OutCentQ1) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainO1
  exact ⟨h1, h2.trans (by decide), comm_of imgRO0 chainO1.2.2.2.1 (by decide) commO1,
    chainK_odd (by decide) (by decide) chainO1 M22OO1.ok⟩

theorem ocent2 : m22OutCentQ2.check = true ∧ m22OutCentQ2.orderCertificate = 1344 ∧
      (m22OutCentWords2.map (evalCodes [m22gA, m22gB])).all
        (fun h => commT 22 (toTable h) (toTable (m22OutReps.getD 1 1))) = true ∧
      oddWitnessOK 22 21 (allTables m22OutCentQ2) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainO2
  exact ⟨h1, h2.trans (by decide), comm_of imgRO1 chainO2.2.2.2.1 (by decide) commO2,
    chainK_odd (by decide) (by decide) chainO2 M22OO2.ok⟩

theorem ofacts : (m22Delta * m22Delta = 1 ∧
      m22Certificate.sift (m22Delta * m22gA * m22Delta⁻¹) 0 = true ∧
      m22Certificate.sift (m22Delta * m22gB * m22Delta⁻¹) 0 = true ∧
      countProducts 22 (commAll 22 [toTable m22gA, toTable m22gB]) (levelTables m22Certificate)
        (toTable m22Delta) = 0
    )
    ∧ (repsOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (cosetOrderTables m22Certificate m22Delta 2) (m22OutReps.map toTable) 2000 = true ∧
      repSizes 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (m22OutReps.map toTable) 2000 = [1386, 330] ∧
      (m22OutReps.map toTable).all (ordTest 22 2) = true
    )
    ∧ (m22OutCentQ1.check = true ∧ m22OutCentQ1.orderCertificate = 320 ∧
      (m22OutCentWords1.map (evalCodes [m22gA, m22gB])).all
        (fun h => commT 22 (toTable h) (toTable (m22OutReps.getD 0 1))) = true ∧
      oddWitnessOK 22 5 (allTables m22OutCentQ1) = true
    )
    ∧ (m22OutCentQ2.check = true ∧ m22OutCentQ2.orderCertificate = 1344 ∧
      (m22OutCentWords2.map (evalCodes [m22gA, m22gB])).all
        (fun h => commT 22 (toTable h) (toTable (m22OutReps.getD 1 1))) = true ∧
      oddWitnessOK 22 21 (allTables m22OutCentQ2) = true
    ) := ⟨delta, ocover, ocent1, ocent2⟩

end CertificateChecks.KernelSporSch.M22OC

end
