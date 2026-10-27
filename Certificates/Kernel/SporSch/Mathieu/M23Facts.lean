
module

public import Certificates.Kernel.SporSch.Mathieu.M23Z
public import CFSG.Certificates.Kernel.SporSch.MathieuBTSound
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23OC

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Th.Native

theorem bindA : bindListK 23 5 (M23Q.S 0) tA = true := by quickRfl

theorem bindB : bindListK 23 5 (M23Q.S 1) tB = true := by quickRfl

theorem pA : permOK 23 5 (mask 5) (23 * 5) (M23Q.S 0) (M23Q.SI 0) = true := by quickRfl

theorem pB : permOK 23 5 (mask 5) (23 * 5) (M23Q.S 1) (M23Q.SI 1) = true := by quickRfl

theorem cA : canonK 23 5 (mask 5) (23 * 5) (M23Q.S 0) = true := by quickRfl

theorem cB : canonK 23 5 (mask 5) (23 * 5) (M23Q.S 1) = true := by quickRfl

theorem ordA : ordIs 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (2 - 1) = true := by quickRfl

theorem ordB : ordIs 23 5 (mask 5) (pidn 23 5) (M23Q.S 1) (4 - 1) = true := by quickRfl

theorem wordsP : wordOrdK 23 5 (mask 5) (pidn 23 5) 2 4 pairWs (M23Q.S 0) (M23Q.S 1) =
    true := by quickRfl

theorem wordsAB : wordOrdK 23 5 (mask 5) (pidn 23 5) 2 4 m23AutWords (M23Q.S 0) (M23Q.S 1) =
    true := by quickRfl

theorem gensC1a : allN 4 (fun j => abOK (m23CentWords1.getD j [])) = true := by quickRfl

theorem gensC1b : allN 4 (fun j => Nat.beq (abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0)
    (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1) (m23CentWords1.getD j [])) (M23C1.S j)) = true := by
  quickRfl

theorem rep0a : abOK (m23InvRepWords.getD 0 []) = true := by quickRfl

theorem rep0b : Nat.beq (abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1)
    (M23Q.SI 1) (m23InvRepWords.getD 0 [])) (M23CK.getD 0 clsD0).R = true := by quickRfl

theorem commC1 : allN 4 (fun j => commK 23 5 (mask 5) (23 * 5) (M23C1.S j)
    (M23CK.getD 0 clsD0).R) = true := by quickRfl

theorem szOK' : szOK 23 5 = true := by quickRfl

theorem tot2 : Nat.beq (sumOrdK 23 5 (mask 5) (ordK M23Q.LR 6) M23B.XL M23B.CL 2 M23B.XL.length)
    3795 = true := by quickRfl

theorem totY : Nat.beq (sumOrdK 23 5 (mask 5) (ordK M23Q.LR 6) M23B.XL M23B.CL 4 M23B.XL.length)
    318780 = true := by quickRfl

theorem totP : Nat.beq (zTotK 23 5 (mask 5) (ordK M23Q.LR 6) M23B.XL M23B.CL M23ZP.SC 23
    M23B.XL.length)
    20401920 = true := by quickRfl

theorem totA : Nat.beq (zTotK 23 5 (mask 5) (ordK M23Q.LR 6) M23B.XL M23B.CL M23ZA.SC 23
    M23B.XL.length)
    10200960 = true := by quickRfl

theorem tA_eq : tA = imageList m23PermA := by decide

theorem tB_eq : tB = imageList m23PermB := by decide

theorem img_of_bind {g : Equiv.Perm (Fin 23)} {l : List Nat} {P : Nat} (hl : l = imageList g)
    (h : bindListK 23 5 P l = true) : imageList g = (unpack 23 5 P).toList := by
  rw [← hl, ← toArray_eq_of_bindListK h]

theorem imgA : imageList m23PermA = (unpack 23 5 (M23Q.S 0)).toList := img_of_bind tA_eq bindA

theorem imgB : imageList m23PermB = (unpack 23 5 (M23Q.S 1)).toList := img_of_bind tB_eq bindB

theorem getD_map_eval (ws : List (List Int)) (S : List (Equiv.Perm (Fin 23))) (j : Nat) :
    (ws.map (evalCodes S)).getD j 1 = evalCodes S (ws.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> rfl

theorem img_word {wd : List Int} {P : Nat} (hw : abOK wd = true)
    (h : Nat.beq (abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1)
      wd) P = true) :
    imageList (evalCodes [m23PermA, m23PermB] wd) = (unpack 23 5 P).toList := by
  rw [abWordK_rep szOK' imgA imgB pA pB hw, Nat.eq_of_beq_eq_true h]

theorem imgRep0 : imageList (m23InvReps.getD 0 1) =
    (unpack 23 5 (M23CK.getD 0 clsD0).R).toList := by
  rw [m23InvReps, getD_map_eval]
  exact img_word rep0a rep0b

theorem elems_of_blocks {f : Nat → Bool} {c nb : Nat} (hc : c ≤ nb * 256)
    (h : ∀ s < nb, allBlk (s * 256) f 256 = true) : ∀ k < c, f k = true := by
  intro k hk
  have hs : k / 256 < nb := by omega
  have := allBlk_spec (h (k / 256) hs) (k % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (k / 256 * 256) (k % 256) = k := by
    change k / 256 * 256 + k % 256 = k
    omega
  rwa [e] at this

theorem clsOK2 : ClsOK 23 5 tA tB 2 4000 M23CK := by
  intro j hj
  have hj1 : j < 1 := by simpa [M23CK] using hj
  interval_cases j
  · exact ⟨M23CK.h0, elems_of_blocks (by decide) M23CK.hb0, fun i hi => absurd hi (by omega)⟩

theorem siftR : ∀ j < M23CK.length, bAnd(canonK 23 5 (mask 5) (23 * 5) (M23CK.getD j clsD0).R,
    siftK 23 5 (mask 5) (23 * 5) (pidn 23 5) M23Q.LR M23Q.TRI M23Q.BP 6 0
      (M23CK.getD j clsD0).R) = true := by
  intro j hj
  have hj1 : j < 1 := by simpa [M23CK] using hj
  interval_cases j
  · quickRfl

theorem chainQ : ChainK 23 5 [m23PermA, m23PermB] m23Words
    (#v[0, 1, 2, 3, 4, 5] : Vector (Fin 23) 6)
    M23Q.S M23Q.SI M23Q.LR M23Q.TR M23Q.TRI 14 M23Q.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M23Q.head, M23Q.hl,
    by norm_num, M23Q.hs⟩
  have hj2 : j < 2 := hj
  interval_cases j
  · exact imgA
  · exact imgB

theorem chainC1 : ChainK 23 5 (m23CentWords1.map (evalCodes [m23PermA, m23PermB]))
    m23CentChainWords1
    (#v[2, 0, 5, 4] : Vector (Fin 23) 4) M23C1.S M23C1.SI M23C1.LR M23C1.TR M23C1.TRI 9 M23C1.BP 2
    16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M23C1.head, M23C1.hl,
    by norm_num, M23C1.hs⟩
  have hj3 : j < 4 := by simpa [m23CentWords1] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensC1a j hj3) (allN_spec gensC1b j hj3)

theorem classEq : ClassEqK 23 5 M23Q.LR M23Q.TR M23Q.TRI M23Q.BP 6 M23B.XL M23B.CL :=
  ⟨rfl, M23B.hr, M23B.hd, M23B.hs⟩

theorem scansZP : ZScans 23 5 2 4 23 pairWs M23B.XL M23CK M23ZP.SC := by
  refine ⟨rfl, fun i hi hord => ?_⟩
  have hi' : i < 16 := hi
  interval_cases i
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n0)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n1)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n2)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n3)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n4)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n5)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n6)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n7)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n8)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n9)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n10)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n11)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n12)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZP.n13)
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 1 := hj
    interval_cases j
    · exact ⟨by decide, M23ZP.h14_0⟩
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 1 := hj
    interval_cases j
    · exact ⟨by decide, M23ZP.h15_0⟩

theorem scansZA : ZScans 23 5 2 4 23 m23AutWords M23B.XL M23CK M23ZA.SC := by
  refine ⟨rfl, fun i hi hord => ?_⟩
  have hi' : i < 16 := hi
  interval_cases i
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n0)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n1)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n2)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n3)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n4)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n5)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n6)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n7)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n8)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n9)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n10)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n11)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n12)
  · exact absurd hord (Nat.ne_of_beq_eq_false M23ZA.n13)
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 1 := hj
    interval_cases j
    · exact ⟨by decide, M23ZA.h14_0⟩
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 1 := hj
    interval_cases j
    · exact ⟨by decide, M23ZA.h15_0⟩

theorem ord2 : (orderTables m23Certificate 2).length = 3795 ∧
    (cosetOrderTables m23Certificate 1 2).length = 3795 := by
  obtain ⟨h1, h2⟩ := classEq_sound (by decide) (by decide) chainQ classEq (mo := 2) (by norm_num)
    (by norm_num)
  exact ⟨h1.trans (Nat.eq_of_beq_eq_true tot2), h2.trans (Nat.eq_of_beq_eq_true tot2)⟩

theorem ordY : (orderTables m23Certificate 4).length = 318780 :=
  (classEq_sound (by decide) (by decide) chainQ classEq (mo := 4) (by norm_num)
    (by norm_num)).1.trans
    (Nat.eq_of_beq_eq_true totY)

theorem hX : (orderTables m23Certificate 2).length = (M23CK.map ClsD.c).sum := by
  rw [ord2.1]
  decide

theorem pair_of_words (x y : Table) : wordsTest 23 2 4 pairWs x y =
    pairTest 23 23 6 2 4 x y := by
  simp [wordsTest, pairTest, pairWs, wordTbls, commWord]

theorem checksQ : m23Certificate.check = true ∧
    m23Certificate.orderCertificate = 10200960 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainQ
  exact ⟨h1, h2.trans (by decide)⟩

theorem wordOrders : ordTest 23 2 (toTable m23PermA) = true ∧
    ordTest 23 4 (toTable m23PermB) = true ∧
    pairTest 23 23 6 2 4 (toTable m23PermA) (toTable m23PermB) = true := by
  refine ⟨ordTest_of_ordIs szOK' imgA cA (by norm_num) ordA,
    ordTest_of_ordIs szOK' imgB cB (by norm_num) ordB, ?_⟩
  rw [← pair_of_words]
  exact wordsTest_of_wordOrdK szOK' imgA imgB wordsP

theorem counts : (orderTables m23Certificate 2).length = 3795 ∧
      (orderTables m23Certificate 4).length = 318780 ∧
      classOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (orderTables m23Certificate 2) 4000 = true ∧
      classTotal 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (orderTables m23Certificate 2) (orderTables m23Certificate 4) 4000 23 6 2 4 =
        20401920 := by
  refine ⟨ord2.1, ordY, classOK_sound (by decide) (by decide) chainQ tA_eq tB_eq clsOK2 siftR
    (by norm_num) hX, ?_⟩
  exact (zClass_sound (by decide) (by decide) chainQ classEq (by norm_num) tA_eq tB_eq clsOK2
    siftR (by norm_num) (by norm_num) (by norm_num) (by norm_num) hX scansZP).trans
    (Nat.eq_of_beq_eq_true totP)

theorem facts2196 : (m23Certificate.check = true)
    ∧ (ordTest 23 2 (toTable m23PermA) = true ∧ ordTest 23 4 (toTable m23PermB) = true ∧
      pairTest 23 23 6 2 4 (toTable m23PermA) (toTable m23PermB) = true
    )
    ∧ ((orderTables m23Certificate 2).length = 3795 ∧
      (orderTables m23Certificate 4).length = 318780 ∧
      classOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (orderTables m23Certificate 2) 4000 = true ∧
      classTotal 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (orderTables m23Certificate 2) (orderTables m23Certificate 4) 4000 23 6 2 4 =
        20401920
    ) := ⟨checksQ.1, wordOrders, counts⟩

theorem hR : m23InvReps.length = M23CK.length ∧ ∀ j < M23CK.length,
    imageList (m23InvReps.getD j 1) = (unpack 23 5 (M23CK.getD j clsD0).R).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj1 : j < 1 := by simpa [M23CK] using hj
  interval_cases j
  · exact imgRep0

theorem cover : repsOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (cosetOrderTables m23Certificate 1 2) (m23InvReps.map toTable) 4000 = true ∧
      repSizes 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (m23InvReps.map toTable) 4000 = [3795] ∧
      (m23InvReps.map toTable).all (ordTest 23 2) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps3 tA_eq tB_eq szOK' clsOK2 hR (by norm_num)
    (X := cosetOrderTables m23Certificate 1 2) (by rw [ord2.2]; decide)
  exact ⟨h1, h2.trans (by decide), h3⟩

theorem comm_of {ws : List (List Int)} {P : Nat → Nat} {R c : Nat} {r : Equiv.Perm (Fin 23)}
    (hr : imageList r = (unpack 23 5 R).toList)
    (hg : ∀ j < (ws.map (evalCodes [m23PermA, m23PermB])).length,
      imageList ((ws.map (evalCodes [m23PermA, m23PermB])).getD j 1) = (unpack 23 5 (P j)).toList)
    (hc : ws.length = c) (hk : allN c (fun j => commK 23 5 (mask 5) (23 * 5) (P j) R) = true) :
    (ws.map (evalCodes [m23PermA, m23PermB])).all (fun h => commT 23 (toTable h) (toTable r)) =
      true := by
  rw [List.all_eq_true]
  intro h hh
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hh
  have himg := hg j hj
  rw [List.getD_eq_getElem _ _ hj] at himg
  exact commT_of_commK himg hr (allN_spec hk j (by simpa [hc] using hj))

theorem cent1 : m23CentQ1.check = true ∧ m23CentQ1.orderCertificate = 2688 ∧
      (m23CentWords1.map (evalCodes [m23PermA, m23PermB])).all
        (fun h => commT 23 (toTable h) (toTable ((m23InvReps).getD 0 1))) = true ∧
      oddWitnessOK 23 21 (allTables m23CentQ1) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainC1
  exact ⟨h1, h2.trans (by decide), comm_of imgRep0 chainC1.2.2.2.1 (by decide) commC1,
    chainK_odd (by decide) (by decide) chainC1 M23O1.ok⟩

theorem aut : ordTest 23 2 (toTable m23PermA) = true ∧ ordTest 23 4 (toTable m23PermB) = true ∧
      wordsTest 23 2 4 m23AutWords (toTable m23PermA) (toTable m23PermB) = true ∧
      repsTotal 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (m23InvReps.map toTable) (orderTables m23Certificate 4) 4000
        (wordsTest 23 2 4 m23AutWords) = 10200960 := by
  refine ⟨ordTest_of_ordIs szOK' imgA cA (by norm_num) ordA,
    ordTest_of_ordIs szOK' imgB cB (by norm_num) ordB,
    wordsTest_of_wordOrdK szOK' imgA imgB wordsAB, ?_⟩
  exact (zReps_sound (by decide) (by decide) chainQ classEq (by norm_num) tA_eq tB_eq clsOK2
    siftR hR (by norm_num) (by norm_num) (by norm_num) (by decide) scansZA).trans
    (Nat.eq_of_beq_eq_true totA)

theorem facts2204 : (repsOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (cosetOrderTables m23Certificate 1 2) (m23InvReps.map toTable) 4000 = true ∧
      repSizes 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (m23InvReps.map toTable) 4000 = [3795] ∧
      (m23InvReps.map toTable).all (ordTest 23 2) = true
    )
    ∧ (m23CentQ1.check = true ∧ m23CentQ1.orderCertificate = 2688 ∧
      (m23CentWords1.map (evalCodes [m23PermA, m23PermB])).all
        (fun h => commT 23 (toTable h) (toTable ((m23InvReps).getD 0 1))) = true ∧
      oddWitnessOK 23 21 (allTables m23CentQ1) = true
    )
    ∧ (ordTest 23 2 (toTable m23PermA) = true ∧ ordTest 23 4 (toTable m23PermB) = true ∧
      wordsTest 23 2 4 m23AutWords (toTable m23PermA) (toTable m23PermB) = true ∧
      repsTotal 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (m23InvReps.map toTable) (orderTables m23Certificate 4) 4000
        (wordsTest 23 2 4 m23AutWords) =
          10200960
    ) := ⟨cover, cent1, aut⟩

end CertificateChecks.KernelSporSch.M23OC

end
