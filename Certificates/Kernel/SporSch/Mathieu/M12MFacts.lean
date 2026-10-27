module

public import Certificates.Kernel.SporSch.Mathieu.M12MData
public import CFSG.Certificates.Kernel.SporSch.MathieuClsSound
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12MOC

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC

theorem bindA : bindListK 24 5 (M12DQ.S 0) tA = true := by quickRfl

theorem bindB : bindListK 24 5 (M12DQ.S 1) tB = true := by quickRfl

theorem bindS : bindListK 24 5 M12S tS = true := by quickRfl

theorem pA : permOK 24 5 (mask 5) (24 * 5) (M12DQ.S 0) (M12DQ.SI 0) = true := by quickRfl

theorem pB : permOK 24 5 (mask 5) (24 * 5) (M12DQ.S 1) (M12DQ.SI 1) = true := by quickRfl

theorem pS : permOK 24 5 (mask 5) (24 * 5) M12S (pinvS 24 5 (mask 5) M12S) = true := by quickRfl

theorem cA : canonK 24 5 (mask 5) (24 * 5) (M12DQ.S 0) = true := by quickRfl

theorem cB : canonK 24 5 (mask 5) (24 * 5) (M12DQ.S 1) = true := by quickRfl

theorem cS : canonK 24 5 (mask 5) (24 * 5) M12S = true := by quickRfl

@[expose] noncomputable def CA : Nat :=
  pcomp 24 5 (mask 5) (pcomp 24 5 (mask 5) M12S (M12DQ.S 0)) (pinvS 24 5 (mask 5) M12S)

@[expose] noncomputable def CB : Nat :=
  pcomp 24 5 (mask 5) (pcomp 24 5 (mask 5) M12S (M12DQ.S 1)) (pinvS 24 5 (mask 5) M12S)

theorem cCA : canonK 24 5 (mask 5) (24 * 5) CA = true := by quickRfl

theorem cCB : canonK 24 5 (mask 5) (24 * 5) CB = true := by quickRfl

theorem siftCA : siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) M12DQ.LR M12DQ.TRI M12DQ.BP 5 0 CA =
    true := by quickRfl

theorem siftCB : siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) M12DQ.LR M12DQ.TRI M12DQ.BP 5 0 CB =
    true := by quickRfl

theorem gensCa : allN 3 (fun j => abOK (m12SigmaCentWords.getD j [])) = true := by quickRfl

theorem gensCb : allN 3 (fun j => Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M12DQ.S 0)
    (M12DQ.SI 0) (M12DQ.S 1) (M12DQ.SI 1) (m12SigmaCentWords.getD j [])) (M12SC.S j)) = true := by
  quickRfl

theorem repS : Nat.beq (M12SCL.getD 0 clsD0).R M12S = true := by quickRfl

theorem commC : allN 3 (fun j => commK 24 5 (mask 5) (24 * 5) (M12SC.S j) M12S) = true := by
  quickRfl


theorem szOK' : szOK 24 5 = true := by quickRfl

theorem tA_eq : tA = imageList m12A1 := by decide

theorem tB_eq : tB = imageList m12B1 := by decide

theorem tS_eq : tS = imageList m12Sigma := by decide

theorem img_of_bind {g : Equiv.Perm (Fin 24)} {l : List Nat} {P : Nat} (hl : l = imageList g)
    (h : bindListK 24 5 P l = true) : imageList g = (unpack 24 5 P).toList := by
  rw [← hl, ← toArray_eq_of_bindListK h]

theorem imgA : imageList m12A1 = (unpack 24 5 (M12DQ.S 0)).toList := img_of_bind tA_eq bindA

theorem imgB : imageList m12B1 = (unpack 24 5 (M12DQ.S 1)).toList := img_of_bind tB_eq bindB

theorem imgS : imageList m12Sigma = (unpack 24 5 M12S).toList := img_of_bind tS_eq bindS

theorem imgSi : imageList m12Sigma⁻¹ = (unpack 24 5 (pinvS 24 5 (mask 5) M12S)).toList :=
  invK_rep imgS pS

theorem imgCA : imageList (m12Sigma * m12A1 * m12Sigma⁻¹) = (unpack 24 5 CA).toList := by
  rw [mulK_rep szOK' (mulK_rep szOK' imgS imgA) imgSi]
  rfl

theorem imgCB : imageList (m12Sigma * m12B1 * m12Sigma⁻¹) = (unpack 24 5 CB).toList := by
  rw [mulK_rep szOK' (mulK_rep szOK' imgS imgB) imgSi]
  rfl

theorem getD_map_eval (ws : List (List Int)) (S : List (Equiv.Perm (Fin 24))) (j : Nat) :
    (ws.map (evalCodes S)).getD j 1 = evalCodes S (ws.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> rfl

theorem img_word {wd : List Int} {P : Nat} (hw : abOK wd = true)
    (h : Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M12DQ.S 0) (M12DQ.SI 0) (M12DQ.S 1)
      (M12DQ.SI 1) wd) P = true) :
    imageList (evalCodes [m12A1, m12B1] wd) = (unpack 24 5 P).toList := by
  rw [abWordK_rep szOK' imgA imgB pA pB hw, Nat.eq_of_beq_eq_true h]

theorem elems_of_blocks {f : Nat → Bool} {c nb : Nat} (hc : c ≤ nb * 256)
    (h : ∀ s < nb, allBlk (s * 256) f 256 = true) : ∀ k < c, f k = true := by
  intro k hk
  have hs : k / 256 < nb := by omega
  have := allBlk_spec (h (k / 256) hs) (k % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (k / 256 * 256) (k % 256) = k := by
    change k / 256 * 256 + k % 256 = k
    omega
  rwa [e] at this

theorem clsOK' : ClsOK 24 5 tA tB 2 1000 M12SCL := by
  intro j hj
  have hj1 : j < 1 := by simpa [M12SCL] using hj
  interval_cases j
  exact ⟨M12SCL.h0, elems_of_blocks (by decide) M12SCL.hb0, fun i hi => absurd hi (by omega)⟩

theorem chainQ : ChainK 24 5 [m12A1, m12B1] m12Words (#v[0, 1, 2, 3, 4] : Vector (Fin 24) 5)
    M12DQ.S M12DQ.SI M12DQ.LR M12DQ.TR M12DQ.TRI 12 M12DQ.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M12DQ.head, M12DQ.hl,
    by norm_num, M12DQ.hs⟩
  have hj2 : j < 2 := hj
  interval_cases j
  · exact imgA
  · exact imgB

theorem chainC : ChainK 24 5 (m12SigmaCentWords.map (evalCodes [m12A1, m12B1]))
    m12SigmaCentChainWords (#v[1, 0, 2] : Vector (Fin 24) 3) M12SC.S M12SC.SI M12SC.LR M12SC.TR
    M12SC.TRI 6 M12SC.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M12SC.head, M12SC.hl,
    by norm_num, M12SC.hs⟩
  have hj3 : j < 3 := by simpa [m12SigmaCentWords] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensCa j hj3) (allN_spec gensCb j hj3)

theorem model : m12D.check = true ∧ m12D.orderCertificate = 95040 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainQ
  exact ⟨h1, h2.trans (by decide)⟩

theorem sigma : m12Sigma * m12Sigma = 1 ∧ m12D.sift (m12Sigma * m12A1 * m12Sigma⁻¹) 0 = true ∧
      m12D.sift (m12Sigma * m12B1 * m12Sigma⁻¹) 0 = true ∧
      countProducts 24 (commAll 24 [toTable m12A1, toTable m12B1]) (levelTables m12D)
        (toTable m12Sigma) = 0 := by
  refine ⟨by decide, chainK_sift (by decide) (by decide) chainQ imgCA cCA siftCA,
    chainK_sift (by decide) (by decide) chainQ imgCB cCB siftCB, ?_⟩
  exact (chainK_commCount (by decide) (by decide) chainQ imgS cS imgA cA imgB cB (by norm_num)
    M12SZ.hc).trans (by decide)

theorem hR : [m12Sigma].length = M12SCL.length ∧ ∀ j < M12SCL.length,
    imageList ([m12Sigma].getD j 1) = (unpack 24 5 (M12SCL.getD j clsD0).R).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj1 : j < 1 := by simpa [M12SCL] using hj
  interval_cases j
  rw [Nat.eq_of_beq_eq_true repS]
  exact imgS

theorem cosetX : (cosetOrderTables m12D m12Sigma 2).length = (M12SX.CS.map List.sum).sum :=
  chainK_cosetCount2 (by decide) (by decide) chainQ imgS cS (by norm_num) (by norm_num) M12SX.hc

theorem cover : repsOK 24 (pairTables m12A1 m12B1) (pairTables m12A1⁻¹ m12B1⁻¹)
        (cosetOrderTables m12D m12Sigma 2) ([m12Sigma].map toTable) 1000 = true ∧
      repSizes 24 (pairTables m12A1 m12B1) (pairTables m12A1⁻¹ m12B1⁻¹)
        ([m12Sigma].map toTable) 1000 = [792] ∧
      ordTest 24 2 (toTable m12Sigma) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps3 tA_eq tB_eq szOK' clsOK' hR (by norm_num)
    (X := cosetOrderTables m12D m12Sigma 2) (by rw [cosetX]; decide)
  refine ⟨h1, h2.trans (by decide), ?_⟩
  simpa using h3

theorem cent : m12SigmaCentQ.check = true ∧ m12SigmaCentQ.orderCertificate = 120 ∧
      (m12SigmaCentWords.map (evalCodes [m12A1, m12B1])).all
        (fun h => commT 24 (toTable h) (toTable m12Sigma)) = true ∧
      oddWitnessOK 24 15 (allTables m12SigmaCentQ) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainC
  refine ⟨h1, h2.trans (by decide), ?_, chainK_odd (by decide) (by decide) chainC M12SO.ok⟩
  rw [List.all_eq_true]
  intro h hh
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hh
  have himg := chainC.2.2.2.1 j hj
  rw [List.getD_eq_getElem _ _ hj] at himg
  exact commT_of_commK himg imgS (allN_spec commC j (by simpa [m12SigmaCentWords] using hj))

theorem facts : (m12D.check = true ∧ m12D.orderCertificate = 95040)
    ∧ (m12Sigma * m12Sigma = 1 ∧ m12D.sift (m12Sigma * m12A1 * m12Sigma⁻¹) 0 = true ∧
      m12D.sift (m12Sigma * m12B1 * m12Sigma⁻¹) 0 = true ∧
      countProducts 24 (commAll 24 [toTable m12A1, toTable m12B1]) (levelTables m12D)
        (toTable m12Sigma) = 0
    )
    ∧ (repsOK 24 (pairTables m12A1 m12B1) (pairTables m12A1⁻¹ m12B1⁻¹)
        (cosetOrderTables m12D m12Sigma 2) ([m12Sigma].map toTable) 1000 = true ∧
      repSizes 24 (pairTables m12A1 m12B1) (pairTables m12A1⁻¹ m12B1⁻¹)
        ([m12Sigma].map toTable) 1000 = [792] ∧
      ordTest 24 2 (toTable m12Sigma) = true
    )
    ∧ (m12SigmaCentQ.check = true ∧ m12SigmaCentQ.orderCertificate = 120 ∧
      (m12SigmaCentWords.map (evalCodes [m12A1, m12B1])).all
        (fun h => commT 24 (toTable h) (toTable m12Sigma)) = true ∧
      oddWitnessOK 24 15 (allTables m12SigmaCentQ) = true
    ) := ⟨model, sigma, cover, cent⟩

end CertificateChecks.KernelSporSch.M12MOC

end
