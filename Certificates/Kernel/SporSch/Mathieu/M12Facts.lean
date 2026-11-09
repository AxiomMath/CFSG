module

public import Certificates.Kernel.SporSch.Mathieu.M12Z
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.Certificates.Kernel.SporSch.MathieuBTSound
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12OC

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT

theorem bindA : bindListK 12 4 (M12Q.S 0) tA = true := by quickRfl

theorem bindB : bindListK 12 4 (M12Q.S 1) tB = true := by quickRfl

theorem pA : permOK 12 4 (mask 4) (12 * 4) (M12Q.S 0) (M12Q.SI 0) = true := by quickRfl

theorem pB : permOK 12 4 (mask 4) (12 * 4) (M12Q.S 1) (M12Q.SI 1) = true := by quickRfl

theorem cA : canonK 12 4 (mask 4) (12 * 4) (M12Q.S 0) = true := by quickRfl

theorem cB : canonK 12 4 (mask 4) (12 * 4) (M12Q.S 1) = true := by quickRfl

theorem cOne : canonK 12 4 (mask 4) (12 * 4) One = true := by quickRfl

theorem gensC1a : allN 4 (fun j => abOK (m12CentWords1.getD j [])) = true := by quickRfl

theorem gensC1b : allN 4 (fun j => Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0)
    (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1) (m12CentWords1.getD j [])) (M12C1.S j)) = true := by
  quickRfl

theorem gensC2a : allN 3 (fun j => abOK (m12CentWords2.getD j [])) = true := by quickRfl

theorem gensC2b : allN 3 (fun j => Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0)
    (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1) (m12CentWords2.getD j [])) (M12C2.S j)) = true := by
  quickRfl

theorem rep0a : abOK (m12InvRepWords.getD 0 []) = true := by quickRfl

theorem rep0b : Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1)
    (M12Q.SI 1) (m12InvRepWords.getD 0 [])) R0 = true := by quickRfl

theorem rep1a : abOK (m12InvRepWords.getD 1 []) = true := by quickRfl

theorem rep1b : Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1)
    (M12Q.SI 1) (m12InvRepWords.getD 1 [])) R1 = true := by quickRfl

theorem commC1 : allN 4 (fun j => commK 12 4 (mask 4) (12 * 4) (M12C1.S j) R0) = true := by
  quickRfl

theorem commC2 : allN 3 (fun j => commK 12 4 (mask 4) (12 * 4) (M12C2.S j) R1) = true := by
  quickRfl

theorem ordA : ordIs 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (2 - 1) = true := by quickRfl

theorem ordB : ordIs 12 4 (mask 4) (pidn 12 4) (M12Q.S 1) (3 - 1) = true := by quickRfl

theorem wordsAB : wordOrdK 12 4 (mask 4) (pidn 12 4) 2 3 m12AutWords (M12Q.S 0) (M12Q.S 1) =
    true := by quickRfl

theorem clsOK' : allC (clsOneR 12 4 tA tB 2 1000) M12CL = true := by quickRfl

theorem disjOK : clsDisj 12 4 M12CL = true := by quickRfl

theorem neOK : allC (fun d => Nat.blt 0 (CFSG.KS.Mathieu.lenN d.2.2.2.2.2.2)) M12CL = true := by
  quickRfl

theorem emptyCls : allC (clsOneR 12 4 tA tB 2 1000)
      [(0, 0, (M12CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1,
        [(M12CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1], [], [], [])] = true ∧
    clsDisj 12 4 [(0, 0, (M12CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1,
        [(M12CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1], [], [], [])] = true ∧
    (allC (fun d => Nat.blt 0 (CFSG.KS.Mathieu.lenN d.2.2.2.2.2.2))
      [(0, 0, (M12CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1,
        [(M12CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1], [], [], [])]).not = true := by
  refine ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem szOK' : szOK 12 4 = true := by quickRfl

theorem tA_eq : tA = imageList m12gA := by decide

theorem tB_eq : tB = imageList m12gB := by decide

theorem img_of_bind {g : Equiv.Perm (Fin 12)} {l : List Nat} {P : Nat} (hl : l = imageList g)
    (h : bindListK 12 4 P l = true) : imageList g = (unpack 12 4 P).toList := by
  rw [← hl, ← toArray_eq_of_bindListK h]

theorem imgA : imageList m12gA = (unpack 12 4 (M12Q.S 0)).toList := img_of_bind tA_eq bindA

theorem imgB : imageList m12gB = (unpack 12 4 (M12Q.S 1)).toList := img_of_bind tB_eq bindB

theorem getD_map_eval (ws : List (List Int)) (S : List (Equiv.Perm (Fin 12))) (j : Nat) :
    (ws.map (evalCodes S)).getD j 1 = evalCodes S (ws.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> rfl

theorem img_word {wd : List Int} {P : Nat} (hw : abOK wd = true)
    (h : Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) (M12Q.S 0) (M12Q.SI 0) (M12Q.S 1) (M12Q.SI 1)
      wd) P = true) :
    imageList (evalCodes [m12gA, m12gB] wd) = (unpack 12 4 P).toList := by
  rw [abWordK_rep szOK' imgA imgB pA pB hw, Nat.eq_of_beq_eq_true h]

theorem imgOne : imageList (1 : Equiv.Perm (Fin 12)) = (unpack 12 4 One).toList := by
  decide

theorem imgRep0 : imageList (m12InvReps.getD 0 1) = (unpack 12 4 R0).toList := by
  rw [m12InvReps, getD_map_eval]
  exact img_word rep0a rep0b

theorem imgRep1 : imageList (m12InvReps.getD 1 1) = (unpack 12 4 R1).toList := by
  rw [m12InvReps, getD_map_eval]
  exact img_word rep1a rep1b

theorem chainQ : ChainK 12 4 [m12gA, m12gB] m12Words (#v[0, 1, 2, 3, 4] : Vector (Fin 12) 5)
    M12Q.S M12Q.SI M12Q.LR M12Q.TR M12Q.TRI 12 M12Q.BP 1 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M12Q.head, M12Q.hl,
    by norm_num, .inl M12Q.hs⟩
  have hj2 : j < 2 := hj
  interval_cases j
  · exact imgA
  · exact imgB

theorem chainC1 : ChainK 12 4 (m12CentWords1.map (evalCodes [m12gA, m12gB])) m12CentChainWords1
    (#v[0, 1, 2] : Vector (Fin 12) 3) M12C1.S M12C1.SI M12C1.LR M12C1.TR M12C1.TRI 8 M12C1.BP 1
    16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M12C1.head, M12C1.hl,
    by norm_num, .inl M12C1.hs⟩
  have hj4 : j < 4 := by simpa [m12CentWords1] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensC1a j hj4) (allN_spec gensC1b j hj4)

theorem chainC2 : ChainK 12 4 (m12CentWords2.map (evalCodes [m12gA, m12gB])) m12CentChainWords2
    (#v[0, 1, 2] : Vector (Fin 12) 3) M12C2.S M12C2.SI M12C2.LR M12C2.TR M12C2.TRI 5 M12C2.BP 1
    16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M12C2.head, M12C2.hl,
    by norm_num, .inl M12C2.hs⟩
  have hj3 : j < 3 := by simpa [m12CentWords2] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensC2a j hj3) (allN_spec gensC2b j hj3)

theorem classEq : ClassEqK 12 4 M12Q.LR M12Q.TR M12Q.TRI M12Q.BP 5 M12BC.XL M12BC.CL :=
  ⟨rfl, M12BC.hr, M12BC.hd, M12BC.hs⟩

theorem tot2 : Nat.beq (sumOrdK 12 4 (mask 4) (ordK M12Q.LR 5) M12BC.XL M12BC.CL 2
    M12BC.XL.length) 891 = true := by quickRfl

theorem cosetX : (cosetOrderTables m12Certificate 1 2).length = 891 :=
  (classEq_sound (by decide) (by decide) chainQ classEq (mo := 2) (by norm_num)
    (by norm_num)).2.trans (Nat.eq_of_beq_eq_true tot2)

theorem hR : m12InvReps.length = M12CL.length ∧ ∀ j < M12CL.length,
    imageList (m12InvReps.getD j 1) =
      (unpack 12 4 (M12CL.getD j (0, 0, 0, [], [], [], [])).2.2.1).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj2 : j < 2 := by simpa [M12CL] using hj
  interval_cases j
  · exact imgRep0
  · exact imgRep1

theorem cover : repsOK 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
        (cosetOrderTables m12Certificate 1 2) (m12InvReps.map toTable) 1000 = true ∧
      repSizes 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
        (m12InvReps.map toTable) 1000 = [495, 396] ∧
      (m12InvReps.map toTable).all (ordTest 12 2) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps tA_eq tB_eq szOK' clsOK' disjOK hR (by norm_num)
    (X := cosetOrderTables m12Certificate 1 2) (by rw [cosetX]; decide) neOK (by norm_num)
  exact ⟨h1, h2.trans (by decide), h3⟩

theorem comm_of {ws : List (List Int)} {P : Nat → Nat} {R c : Nat} {r : Equiv.Perm (Fin 12)}
    (hr : imageList r = (unpack 12 4 R).toList)
    (hg : ∀ j < (ws.map (evalCodes [m12gA, m12gB])).length,
      imageList ((ws.map (evalCodes [m12gA, m12gB])).getD j 1) = (unpack 12 4 (P j)).toList)
    (hc : ws.length = c) (hk : allN c (fun j => commK 12 4 (mask 4) (12 * 4) (P j) R) = true) :
    (ws.map (evalCodes [m12gA, m12gB])).all (fun h => commT 12 (toTable h) (toTable r)) =
      true := by
  rw [List.all_eq_true]
  intro h hh
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hh
  have himg := hg j hj
  rw [List.getD_eq_getElem _ _ hj] at himg
  exact commT_of_commK himg hr (allN_spec hk j (by simpa [hc] using hj))

theorem cent1 : m12CentQ1.check = true ∧ m12CentQ1.orderCertificate = 192 ∧
      (m12CentWords1.map (evalCodes [m12gA, m12gB])).all
        (fun h => commT 12 (toTable h) (toTable ((m12InvReps).getD 0 1))) = true ∧
      oddWitnessOK 12 3 (allTables m12CentQ1) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainC1
  exact ⟨h1, h2.trans (by decide), comm_of imgRep0 chainC1.2.2.2.1 (by decide) commC1,
    chainK_odd (by decide) (by decide) chainC1 M12O1.ok⟩

theorem cent2 : m12CentQ2.check = true ∧ m12CentQ2.orderCertificate = 240 ∧
      (m12CentWords2.map (evalCodes [m12gA, m12gB])).all
        (fun h => commT 12 (toTable h) (toTable ((m12InvReps).getD 1 1))) = true ∧
      oddWitnessOK 12 15 (allTables m12CentQ2) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainC2
  exact ⟨h1, h2.trans (by decide), comm_of imgRep1 chainC2.2.2.2.1 (by decide) commC2,
    chainK_odd (by decide) (by decide) chainC2 M12O2.ok⟩

theorem elems_of_blocks {f : Nat → Bool} {c nb : Nat} (hc : c ≤ nb * 256)
    (h : ∀ s < nb, allBlk (s * 256) f 256 = true) : ∀ k < c, f k = true := by
  intro k hk
  have hs : k / 256 < nb := by omega
  have := allBlk_spec (h (k / 256) hs) (k % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (k / 256 * 256) (k % 256) = k := by
    change k / 256 * 256 + k % 256 = k
    omega
  rwa [e] at this

theorem clsOK2 : ClsOK 12 4 tA tB 2 1000 M12CK := by
  intro j hj
  have hj1 : j < 2 := by simpa [M12CK] using hj
  interval_cases j
  · exact ⟨M12CK.h0, elems_of_blocks (by decide) M12CK.hb0, fun i hi => absurd hi (by omega)⟩
  · exact ⟨M12CK.h1, elems_of_blocks (by decide) M12CK.hb1, fun i hi => by
      have hi1 : i < 1 := hi
      interval_cases i
      exact M12CK.n1_0⟩

theorem siftR : ∀ j < M12CK.length, bAnd(canonK 12 4 (mask 4) (12 * 4) (M12CK.getD j clsD0).R,
    siftK 12 4 (mask 4) (12 * 4) (pidn 12 4) M12Q.LR M12Q.TRI M12Q.BP 5 0
      (M12CK.getD j clsD0).R) = true := by
  intro j hj
  have hj1 : j < 2 := by simpa [M12CK] using hj
  interval_cases j
  · quickRfl
  · quickRfl

theorem repCK0 : Nat.beq (M12CK.getD 0 clsD0).R R0 = true := by quickRfl

theorem repCK1 : Nat.beq (M12CK.getD 1 clsD0).R R1 = true := by quickRfl

theorem hRK : m12InvReps.length = M12CK.length ∧ ∀ j < M12CK.length,
    imageList (m12InvReps.getD j 1) = (unpack 12 4 (M12CK.getD j clsD0).R).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj1 : j < 2 := by simpa [M12CK] using hj
  interval_cases j
  · rw [Nat.eq_of_beq_eq_true repCK0]
    exact imgRep0
  · rw [Nat.eq_of_beq_eq_true repCK1]
    exact imgRep1

theorem scansZA : ZScans 12 4 2 3 11 m12AutWords M12BC.XL M12CK M12ZA.SC := by
  refine ⟨rfl, fun i hi hord => ?_⟩
  have hi' : i < 14 := hi
  interval_cases i
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n0)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n1)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n2)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n3)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n4)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n5)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n6)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n7)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n8)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n9)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n10)
  · exact absurd hord (Nat.ne_of_beq_eq_false M12ZA.n11)
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 2 := hj
    interval_cases j
    · exact ⟨by decide, M12ZA.h12_0⟩
    · exact ⟨by decide, M12ZA.h12_1⟩
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 2 := hj
    interval_cases j
    · exact ⟨by decide, M12ZA.h13_0⟩
    · exact ⟨by decide, M12ZA.h13_1⟩

theorem totA : Nat.beq (zTotK 12 4 (mask 4) (ordK M12Q.LR 5) M12BC.XL M12BC.CL M12ZA.SC 11
    M12BC.XL.length) 190080 = true := by quickRfl

theorem aut : ordTest 12 2 (toTable m12gA) = true ∧ ordTest 12 3 (toTable m12gB) = true ∧
      wordsTest 12 2 3 m12AutWords (toTable m12gA) (toTable m12gB) = true ∧
      repsTotal 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
        (m12InvReps.map toTable) (orderTables m12Certificate 3) 1000
        (wordsTest 12 2 3 m12AutWords) = 190080 := by
  refine ⟨ordTest_of_ordIs szOK' imgA cA (by norm_num) ordA,
    ordTest_of_ordIs szOK' imgB cB (by norm_num) ordB,
    wordsTest_of_wordOrdK szOK' imgA imgB wordsAB, ?_⟩
  exact (zReps_sound (by decide) (by decide) chainQ classEq (by norm_num) tA_eq tB_eq clsOK2
    siftR hRK (by norm_num) (by norm_num) (by norm_num) (by decide) scansZA).trans
    (Nat.eq_of_beq_eq_true totA)

theorem facts : (repsOK 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
        (cosetOrderTables m12Certificate 1 2) (m12InvReps.map toTable) 1000 = true ∧
      repSizes 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
        (m12InvReps.map toTable) 1000 = [495, 396] ∧
      (m12InvReps.map toTable).all (ordTest 12 2) = true
    )
    ∧ (m12CentQ1.check = true ∧ m12CentQ1.orderCertificate = 192 ∧
      (m12CentWords1.map (evalCodes [m12gA, m12gB])).all
        (fun h => commT 12 (toTable h) (toTable ((m12InvReps).getD 0 1))) = true ∧
      oddWitnessOK 12 3 (allTables m12CentQ1) = true
    )
    ∧ (m12CentQ2.check = true ∧ m12CentQ2.orderCertificate = 240 ∧
      (m12CentWords2.map (evalCodes [m12gA, m12gB])).all
        (fun h => commT 12 (toTable h) (toTable ((m12InvReps).getD 1 1))) = true ∧
      oddWitnessOK 12 15 (allTables m12CentQ2) = true
    )
    ∧ (ordTest 12 2 (toTable m12gA) = true ∧ ordTest 12 3 (toTable m12gB) = true ∧
      wordsTest 12 2 3 m12AutWords (toTable m12gA) (toTable m12gB) = true ∧
      repsTotal 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
        (m12InvReps.map toTable) (orderTables m12Certificate 3) 1000 (wordsTest 12 2 3 m12AutWords) =
          190080
    ) := ⟨cover, cent1, cent2, aut⟩

end CertificateChecks.KernelSporSch.M12OC

end
