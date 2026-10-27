
module

public import Certificates.Kernel.SporSch.Mathieu.M24Z
public import Certificates.Kernel.SporSch.Mathieu.M24Odd
public import CFSG.Certificates.Kernel.SporSch.MathieuBTSound
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M24OC

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Th.Native

theorem bindA : bindListK 24 5 (M24Q.S 0) tA = true := by quickRfl

theorem bindB : bindListK 24 5 (M24Q.S 1) tB = true := by quickRfl

theorem pA : permOK 24 5 (mask 5) (24 * 5) (M24Q.S 0) (M24Q.SI 0) = true := by quickRfl

theorem pB : permOK 24 5 (mask 5) (24 * 5) (M24Q.S 1) (M24Q.SI 1) = true := by quickRfl

theorem cA : canonK 24 5 (mask 5) (24 * 5) (M24Q.S 0) = true := by quickRfl

theorem cB : canonK 24 5 (mask 5) (24 * 5) (M24Q.S 1) = true := by quickRfl

theorem ordA : ordIs 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (2 - 1) = true := by quickRfl

theorem ordB : ordIs 24 5 (mask 5) (pidn 24 5) (M24Q.S 1) (3 - 1) = true := by quickRfl

theorem wordsP : wordOrdK 24 5 (mask 5) (pidn 24 5) 2 3 pairWs (M24Q.S 0) (M24Q.S 1) =
    true := by quickRfl

theorem wordsAB : wordOrdK 24 5 (mask 5) (pidn 24 5) 2 3 m24AutWords (M24Q.S 0) (M24Q.S 1) =
    true := by quickRfl

theorem gensC1a : allN 3 (fun j => abOK (m24CentWords1.getD j [])) = true := by quickRfl

theorem gensC1b : allN 3 (fun j => Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0)
    (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1) (m24CentWords1.getD j [])) (M24C1.S j)) = true := by
  quickRfl

theorem rep0a : abOK (m24InvRepWords.getD 0 []) = true := by quickRfl

theorem rep0b : Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1)
    (M24Q.SI 1) (m24InvRepWords.getD 0 [])) (M24CK.getD 0 clsD0).R = true := by quickRfl

theorem commC1 : allN 3 (fun j => commK 24 5 (mask 5) (24 * 5) (M24C1.S j)
    (M24CK.getD 0 clsD0).R) = true := by quickRfl

theorem gensC2a : allN 2 (fun j => abOK (m24CentWords2.getD j [])) = true := by quickRfl

theorem gensC2b : allN 2 (fun j => Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0)
    (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1) (m24CentWords2.getD j [])) (M24C2.S j)) = true := by
  quickRfl

theorem rep1a : abOK (m24InvRepWords.getD 1 []) = true := by quickRfl

theorem rep1b : Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1)
    (M24Q.SI 1) (m24InvRepWords.getD 1 [])) (M24CK.getD 1 clsD0).R = true := by quickRfl

theorem commC2 : allN 2 (fun j => commK 24 5 (mask 5) (24 * 5) (M24C2.S j)
    (M24CK.getD 1 clsD0).R) = true := by quickRfl

theorem szOK' : szOK 24 5 = true := by quickRfl

theorem tot2 : Nat.beq (sumOrdK 24 5 (mask 5) (ordK M24Q.LR 7) M24B.XL M24B.CL 2 M24B.XL.length)
    43263 = true := by quickRfl

theorem totY : Nat.beq (sumOrdK 24 5 (mask 5) (ordK M24Q.LR 7) M24B.XL M24B.CL 3 M24B.XL.length)
    712448 = true := by quickRfl

theorem totP : Nat.beq (zTotK 24 5 (mask 5) (ordK M24Q.LR 7) M24B.XL M24B.CL M24ZP.SC 23
    M24B.XL.length)
    979292160 = true := by quickRfl

theorem totA : Nat.beq (zTotK 24 5 (mask 5) (ordK M24Q.LR 7) M24B.XL M24B.CL M24ZA.SC 23
    M24B.XL.length)
    244823040 = true := by quickRfl

theorem tA_eq : tA = imageList m24gA := by decide

theorem tB_eq : tB = imageList m24gB := by decide

theorem img_of_bind {g : Equiv.Perm (Fin 24)} {l : List Nat} {P : Nat} (hl : l = imageList g)
    (h : bindListK 24 5 P l = true) : imageList g = (unpack 24 5 P).toList := by
  rw [← hl, ← toArray_eq_of_bindListK h]

theorem imgA : imageList m24gA = (unpack 24 5 (M24Q.S 0)).toList := img_of_bind tA_eq bindA

theorem imgB : imageList m24gB = (unpack 24 5 (M24Q.S 1)).toList := img_of_bind tB_eq bindB

theorem getD_map_eval (ws : List (List Int)) (S : List (Equiv.Perm (Fin 24))) (j : Nat) :
    (ws.map (evalCodes S)).getD j 1 = evalCodes S (ws.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> rfl

theorem img_word {wd : List Int} {P : Nat} (hw : abOK wd = true)
    (h : Nat.beq (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1)
      wd) P = true) :
    imageList (evalCodes [m24gA, m24gB] wd) = (unpack 24 5 P).toList := by
  rw [abWordK_rep szOK' imgA imgB pA pB hw, Nat.eq_of_beq_eq_true h]

theorem imgRep0 : imageList (m24InvReps.getD 0 1) =
    (unpack 24 5 (M24CK.getD 0 clsD0).R).toList := by
  rw [m24InvReps, getD_map_eval]
  exact img_word rep0a rep0b

theorem imgRep1 : imageList (m24InvReps.getD 1 1) =
    (unpack 24 5 (M24CK.getD 1 clsD0).R).toList := by
  rw [m24InvReps, getD_map_eval]
  exact img_word rep1a rep1b

theorem elems_of_blocks {f : Nat → Bool} {c nb : Nat} (hc : c ≤ nb * 256)
    (h : ∀ s < nb, allBlk (s * 256) f 256 = true) : ∀ k < c, f k = true := by
  intro k hk
  have hs : k / 256 < nb := by omega
  have := allBlk_spec (h (k / 256) hs) (k % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (k / 256 * 256) (k % 256) = k := by
    change k / 256 * 256 + k % 256 = k
    omega
  rwa [e] at this

theorem clsOK2 : ClsOK 24 5 tA tB 2 40000 M24CK := by
  intro j hj
  have hj1 : j < 2 := by simpa [M24CK] using hj
  interval_cases j
  · exact ⟨M24CK.h0, elems_of_blocks (by decide) M24CK.hb0, fun i hi => absurd hi (by omega)⟩
  · exact ⟨M24CK.h1, elems_of_blocks (by decide) M24CK.hb1, fun i hi => by
      have hi1 : i < 1 := hi
      interval_cases i
      exact M24CK.n1_0⟩

theorem siftR : ∀ j < M24CK.length, bAnd(canonK 24 5 (mask 5) (24 * 5) (M24CK.getD j clsD0).R,
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) M24Q.LR M24Q.TRI M24Q.BP 7 0
      (M24CK.getD j clsD0).R) = true := by
  intro j hj
  have hj1 : j < 2 := by simpa [M24CK] using hj
  interval_cases j
  · quickRfl
  · quickRfl

theorem chainQ : ChainK 24 5 [m24gA, m24gB] m24Words
    (#v[0, 1, 2, 3, 4, 5, 6] : Vector (Fin 24) 7)
    M24Q.S M24Q.SI M24Q.LR M24Q.TR M24Q.TRI 11 M24Q.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M24Q.head, M24Q.hl,
    by norm_num, M24Q.hs⟩
  have hj2 : j < 2 := hj
  interval_cases j
  · exact imgA
  · exact imgB

theorem chainC1 : ChainK 24 5 (m24CentWords1.map (evalCodes [m24gA, m24gB]))
    m24CentChainWords1
    (#v[0, 1, 2] : Vector (Fin 24) 3) M24C1.S M24C1.SI M24C1.LR M24C1.TR M24C1.TRI 8 M24C1.BP 2
    16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M24C1.head, M24C1.hl,
    by norm_num, M24C1.hs⟩
  have hj3 : j < 3 := by simpa [m24CentWords1] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensC1a j hj3) (allN_spec gensC1b j hj3)

theorem chainC2 : ChainK 24 5 (m24CentWords2.map (evalCodes [m24gA, m24gB]))
    m24CentChainWords2
    (#v[1, 0, 2, 3] : Vector (Fin 24) 4) M24C2.S M24C2.SI M24C2.LR M24C2.TR M24C2.TRI 7 M24C2.BP 2
    16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M24C2.head, M24C2.hl,
    by norm_num, M24C2.hs⟩
  have hj3 : j < 2 := by simpa [m24CentWords2] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensC2a j hj3) (allN_spec gensC2b j hj3)

theorem classEq : ClassEqK 24 5 M24Q.LR M24Q.TR M24Q.TRI M24Q.BP 7 M24B.XL M24B.CL :=
  ⟨rfl, M24B.hr, M24B.hd, M24B.hs⟩

theorem scansZP : ZScans 24 5 2 3 23 pairWs M24B.XL M24CK M24ZP.SC := by
  refine ⟨rfl, fun i hi hord => ?_⟩
  have hi' : i < 25 := hi
  interval_cases i
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n0)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n1)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n2)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n3)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n4)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n5)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n6)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n7)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n8)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n9)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n10)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n11)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n12)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n13)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n14)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n15)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n16)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n17)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n18)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n19)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n20)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n21)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZP.n22)
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 2 := hj
    interval_cases j
    · exact ⟨by decide, M24ZP.h23_0⟩
    · exact ⟨by decide, M24ZP.h23_1⟩
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 2 := hj
    interval_cases j
    · exact ⟨by decide, M24ZP.h24_0⟩
    · exact ⟨by decide, M24ZP.h24_1⟩

theorem scansZA : ZScans 24 5 2 3 23 m24AutWords M24B.XL M24CK M24ZA.SC := by
  refine ⟨rfl, fun i hi hord => ?_⟩
  have hi' : i < 25 := hi
  interval_cases i
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n0)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n1)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n2)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n3)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n4)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n5)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n6)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n7)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n8)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n9)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n10)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n11)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n12)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n13)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n14)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n15)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n16)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n17)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n18)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n19)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n20)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n21)
  · exact absurd hord (Nat.ne_of_beq_eq_false M24ZA.n22)
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 2 := hj
    interval_cases j
    · exact ⟨by decide, M24ZA.h23_0⟩
    · exact ⟨by decide, M24ZA.h23_1⟩
  · refine ⟨rfl, fun j hj => ?_⟩
    have hj' : j < 2 := hj
    interval_cases j
    · exact ⟨by decide, M24ZA.h24_0⟩
    · exact ⟨by decide, M24ZA.h24_1⟩

theorem ord2 : (orderTables m24Certificate 2).length = 43263 ∧
    (cosetOrderTables m24Certificate 1 2).length = 43263 := by
  obtain ⟨h1, h2⟩ := classEq_sound (by decide) (by decide) chainQ classEq (mo := 2) (by norm_num)
    (by norm_num)
  exact ⟨h1.trans (Nat.eq_of_beq_eq_true tot2), h2.trans (Nat.eq_of_beq_eq_true tot2)⟩

theorem ordY : (orderTables m24Certificate 3).length = 712448 :=
  (classEq_sound (by decide) (by decide) chainQ classEq (mo := 3) (by norm_num)
    (by norm_num)).1.trans
    (Nat.eq_of_beq_eq_true totY)

theorem hX : (orderTables m24Certificate 2).length = (M24CK.map ClsD.c).sum := by
  rw [ord2.1]
  decide

theorem pair_of_words (x y : Table) : wordsTest 24 2 3 pairWs x y =
    pairTest 24 23 12 2 3 x y := by
  simp [wordsTest, pairTest, pairWs, wordTbls, commWord]

theorem checksQ : m24Certificate.check = true ∧
    m24Certificate.orderCertificate = 244823040 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainQ
  exact ⟨h1, h2.trans (by decide)⟩

theorem wordOrders : ordTest 24 2 (toTable m24gA) = true ∧
    ordTest 24 3 (toTable m24gB) = true ∧
    pairTest 24 23 12 2 3 (toTable m24gA) (toTable m24gB) = true := by
  refine ⟨ordTest_of_ordIs szOK' imgA cA (by norm_num) ordA,
    ordTest_of_ordIs szOK' imgB cB (by norm_num) ordB, ?_⟩
  rw [← pair_of_words]
  exact wordsTest_of_wordOrdK szOK' imgA imgB wordsP

theorem counts : (orderTables m24Certificate 2).length = 43263 ∧
      (orderTables m24Certificate 3).length = 712448 ∧
      classOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (orderTables m24Certificate 2) 40000 = true ∧
      classTotal 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (orderTables m24Certificate 2) (orderTables m24Certificate 3) 40000 23 12 2 3 =
        979292160 := by
  refine ⟨ord2.1, ordY, classOK_sound (by decide) (by decide) chainQ tA_eq tB_eq clsOK2 siftR
    (by norm_num) hX, ?_⟩
  exact (zClass_sound (by decide) (by decide) chainQ classEq (by norm_num) tA_eq tB_eq clsOK2
    siftR (by norm_num) (by norm_num) (by norm_num) (by norm_num) hX scansZP).trans
    (Nat.eq_of_beq_eq_true totP)

theorem facts2198 : (m24Certificate.check = true)
    ∧ (ordTest 24 2 (toTable m24gA) = true ∧ ordTest 24 3 (toTable m24gB) = true ∧
      pairTest 24 23 12 2 3 (toTable m24gA) (toTable m24gB) = true
    )
    ∧ ((orderTables m24Certificate 2).length = 43263 ∧
      (orderTables m24Certificate 3).length = 712448 ∧
      classOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (orderTables m24Certificate 2) 40000 = true ∧
      classTotal 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (orderTables m24Certificate 2) (orderTables m24Certificate 3) 40000 23 12 2 3 =
        979292160
    ) := ⟨checksQ.1, wordOrders, counts⟩

theorem hR : m24InvReps.length = M24CK.length ∧ ∀ j < M24CK.length,
    imageList (m24InvReps.getD j 1) = (unpack 24 5 (M24CK.getD j clsD0).R).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj1 : j < 2 := by simpa [M24CK] using hj
  interval_cases j
  · exact imgRep0
  · exact imgRep1

theorem cover : repsOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (cosetOrderTables m24Certificate 1 2) (m24InvReps.map toTable) 40000 = true ∧
      repSizes 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (m24InvReps.map toTable) 40000 = [31878, 11385] ∧
      (m24InvReps.map toTable).all (ordTest 24 2) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps3 tA_eq tB_eq szOK' clsOK2 hR (by norm_num)
    (X := cosetOrderTables m24Certificate 1 2) (by rw [ord2.2]; decide)
  exact ⟨h1, h2.trans (by decide), h3⟩

theorem comm_of {ws : List (List Int)} {P : Nat → Nat} {R c : Nat} {r : Equiv.Perm (Fin 24)}
    (hr : imageList r = (unpack 24 5 R).toList)
    (hg : ∀ j < (ws.map (evalCodes [m24gA, m24gB])).length,
      imageList ((ws.map (evalCodes [m24gA, m24gB])).getD j 1) = (unpack 24 5 (P j)).toList)
    (hc : ws.length = c) (hk : allN c (fun j => commK 24 5 (mask 5) (24 * 5) (P j) R) = true) :
    (ws.map (evalCodes [m24gA, m24gB])).all (fun h => commT 24 (toTable h) (toTable r)) =
      true := by
  rw [List.all_eq_true]
  intro h hh
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hh
  have himg := hg j hj
  rw [List.getD_eq_getElem _ _ hj] at himg
  exact commT_of_commK himg hr (allN_spec hk j (by simpa [hc] using hj))

theorem cent1 : m24CentQ1.check = true ∧ m24CentQ1.orderCertificate = 7680 ∧
      (m24CentWords1.map (evalCodes [m24gA, m24gB])).all
        (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 0 1))) = true ∧
      oddWitnessOK 24 15 (allTables m24CentQ1) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainC1
  exact ⟨h1, h2.trans (by decide), comm_of imgRep0 chainC1.2.2.2.1 (by decide) commC1,
    chainK_oddB (by decide) (by decide) chainC1 (by decide) M24O1.hb⟩

theorem cent2 : m24CentQ2.check = true ∧ m24CentQ2.orderCertificate = 21504 ∧
      (m24CentWords2.map (evalCodes [m24gA, m24gB])).all
        (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 1 1))) = true ∧
      oddWitnessOK 24 21 (allTables m24CentQ2) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainC2
  exact ⟨h1, h2.trans (by decide), comm_of imgRep1 chainC2.2.2.2.1 (by decide) commC2,
    chainK_oddB (by decide) (by decide) chainC2 (by decide) M24O2.hb⟩

theorem aut : ordTest 24 2 (toTable m24gA) = true ∧ ordTest 24 3 (toTable m24gB) = true ∧
      wordsTest 24 2 3 m24AutWords (toTable m24gA) (toTable m24gB) = true ∧
      repsTotal 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (m24InvReps.map toTable) (orderTables m24Certificate 3) 40000
        (wordsTest 24 2 3 m24AutWords) = 244823040 := by
  refine ⟨ordTest_of_ordIs szOK' imgA cA (by norm_num) ordA,
    ordTest_of_ordIs szOK' imgB cB (by norm_num) ordB,
    wordsTest_of_wordOrdK szOK' imgA imgB wordsAB, ?_⟩
  exact (zReps_sound (by decide) (by decide) chainQ classEq (by norm_num) tA_eq tB_eq clsOK2
    siftR hR (by norm_num) (by norm_num) (by norm_num) (by decide) scansZA).trans
    (Nat.eq_of_beq_eq_true totA)

theorem facts2205 : (repsOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (cosetOrderTables m24Certificate 1 2) (m24InvReps.map toTable) 40000 = true ∧
      repSizes 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (m24InvReps.map toTable) 40000 = [31878, 11385] ∧
      (m24InvReps.map toTable).all (ordTest 24 2) = true
    )
    ∧ (m24CentQ1.check = true ∧ m24CentQ1.orderCertificate = 7680 ∧
      (m24CentWords1.map (evalCodes [m24gA, m24gB])).all
        (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 0 1))) = true ∧
      oddWitnessOK 24 15 (allTables m24CentQ1) = true
    )
    ∧ (m24CentQ2.check = true ∧ m24CentQ2.orderCertificate = 21504 ∧
      (m24CentWords2.map (evalCodes [m24gA, m24gB])).all
        (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 1 1))) = true ∧
      oddWitnessOK 24 21 (allTables m24CentQ2) = true
    )
    ∧ (ordTest 24 2 (toTable m24gA) = true ∧ ordTest 24 3 (toTable m24gB) = true ∧
      wordsTest 24 2 3 m24AutWords (toTable m24gA) (toTable m24gB) = true ∧
      repsTotal 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (m24InvReps.map toTable) (orderTables m24Certificate 3) 40000
        (wordsTest 24 2 3 m24AutWords) =
          244823040
    ) := ⟨cover, cent1, cent2, aut⟩

end CertificateChecks.KernelSporSch.M24OC

end
