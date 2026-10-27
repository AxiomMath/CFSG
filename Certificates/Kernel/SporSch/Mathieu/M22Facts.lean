module

public import Certificates.Kernel.SporSch.Mathieu.M22X
public import Certificates.Kernel.SporSch.Mathieu.M22Y
public import Certificates.Kernel.SporSch.Mathieu.M22Cls
public import CFSG.Certificates.Kernel.SporSch.MathieuClsSound
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2FSound
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22OC

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC

theorem bindA : bindListK 22 5 (M22Q.S 0) tA = true := by quickRfl

theorem bindB : bindListK 22 5 (M22Q.S 1) tB = true := by quickRfl

theorem pA : permOK 22 5 (mask 5) (22 * 5) (M22Q.S 0) (M22Q.SI 0) = true := by quickRfl

theorem pB : permOK 22 5 (mask 5) (22 * 5) (M22Q.S 1) (M22Q.SI 1) = true := by quickRfl

theorem cA : canonK 22 5 (mask 5) (22 * 5) (M22Q.S 0) = true := by quickRfl

theorem cB : canonK 22 5 (mask 5) (22 * 5) (M22Q.S 1) = true := by quickRfl

theorem cOne : canonK 22 5 (mask 5) (22 * 5) One = true := by quickRfl

theorem gensC1a : allN 3 (fun j => abOK (m22CentWords1.getD j [])) = true := by quickRfl

theorem gensC1b : allN 3 (fun j => Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0)
    (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1) (m22CentWords1.getD j [])) (M22C1.S j)) = true := by
  quickRfl

theorem rep0a : abOK (m22InvRepWords.getD 0 []) = true := by quickRfl

theorem rep0b : Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1)
    (M22Q.SI 1) (m22InvRepWords.getD 0 [])) R0 = true := by quickRfl

theorem commC1 : allN 3 (fun j => commK 22 5 (mask 5) (22 * 5) (M22C1.S j) R0) = true := by
  quickRfl

theorem ordA : ordIs 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (2 - 1) = true := by quickRfl

theorem ordB : ordIs 22 5 (mask 5) (pidn 22 5) (M22Q.S 1) (4 - 1) = true := by quickRfl

theorem wordsAB : wordOrdK 22 5 (mask 5) (pidn 22 5) 2 4 m22AutWords (M22Q.S 0) (M22Q.S 1) =
    true := by quickRfl

theorem repCK : Nat.beq (M22CK.getD 0 clsD0).R R0 = true := by quickRfl

theorem szOK' : szOK 22 5 = true := by quickRfl

theorem tA_eq : tA = imageList m22gA := by decide

theorem tB_eq : tB = imageList m22gB := by decide

theorem img_of_bind {g : Equiv.Perm (Fin 22)} {l : List Nat} {P : Nat} (hl : l = imageList g)
    (h : bindListK 22 5 P l = true) : imageList g = (unpack 22 5 P).toList := by
  rw [← hl, ← toArray_eq_of_bindListK h]

theorem imgA : imageList m22gA = (unpack 22 5 (M22Q.S 0)).toList := img_of_bind tA_eq bindA

theorem imgB : imageList m22gB = (unpack 22 5 (M22Q.S 1)).toList := img_of_bind tB_eq bindB

theorem getD_map_eval (ws : List (List Int)) (S : List (Equiv.Perm (Fin 22))) (j : Nat) :
    (ws.map (evalCodes S)).getD j 1 = evalCodes S (ws.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> rfl

theorem img_word {wd : List Int} {P : Nat} (hw : abOK wd = true)
    (h : Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1) (M22Q.SI 1)
      wd) P = true) :
    imageList (evalCodes [m22gA, m22gB] wd) = (unpack 22 5 P).toList := by
  rw [abWordK_rep szOK' imgA imgB pA pB hw, Nat.eq_of_beq_eq_true h]

theorem imgOne : imageList (1 : Equiv.Perm (Fin 22)) = (unpack 22 5 One).toList := by
  decide

theorem imgRep0 : imageList (m22InvReps.getD 0 1) = (unpack 22 5 R0).toList := by
  rw [m22InvReps, getD_map_eval]
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

theorem clsOK2 : ClsOK 22 5 tA tB 2 2000 M22CK := by
  intro j hj
  have hj1 : j < 1 := by simpa [M22CK] using hj
  interval_cases j
  exact ⟨M22CK.h0, elems_of_blocks (by decide) M22CK.hb0, fun i hi => absurd hi (by omega)⟩

theorem chainQ : ChainK 22 5 [m22gA, m22gB] m22Words (#v[0, 1, 2, 3, 4] : Vector (Fin 22) 5)
    M22Q.S M22Q.SI M22Q.LR M22Q.TR M22Q.TRI 13 M22Q.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M22Q.head, M22Q.hl,
    by norm_num, M22Q.hs⟩
  have hj2 : j < 2 := hj
  interval_cases j
  · exact imgA
  · exact imgB

theorem chainC1 : ChainK 22 5 (m22CentWords1.map (evalCodes [m22gA, m22gB])) m22CentChainWords1
    (#v[0, 1, 2] : Vector (Fin 22) 3) M22C1.S M22C1.SI M22C1.LR M22C1.TR M22C1.TRI 6 M22C1.BP 2
    16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, M22C1.head, M22C1.hl,
    by norm_num, M22C1.hs⟩
  have hj3 : j < 3 := by simpa [m22CentWords1] using hj
  rw [getD_map_eval]
  exact img_word (allN_spec gensC1a j hj3) (allN_spec gensC1b j hj3)

theorem cosetX : (cosetOrderTables m22Certificate 1 2).length = (M22X.CS.map List.sum).sum :=
  chainK_cosetCount2 (by decide) (by decide) chainQ imgOne cOne (by norm_num) (by norm_num) M22X.hc

theorem hR : m22InvReps.length = M22CK.length ∧ ∀ j < M22CK.length,
    imageList (m22InvReps.getD j 1) = (unpack 22 5 (M22CK.getD j clsD0).R).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj1 : j < 1 := by simpa [M22CK] using hj
  interval_cases j
  rw [Nat.eq_of_beq_eq_true repCK]
  exact imgRep0

theorem cover : repsOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (cosetOrderTables m22Certificate 1 2) (m22InvReps.map toTable) 2000 = true ∧
      repSizes 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (m22InvReps.map toTable) 2000 = [1155] ∧
      (m22InvReps.map toTable).all (ordTest 22 2) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps3 tA_eq tB_eq szOK' clsOK2 hR (by norm_num)
    (X := cosetOrderTables m22Certificate 1 2) (by rw [cosetX]; decide)
  exact ⟨h1, h2.trans (by decide), h3⟩

theorem comm_of {ws : List (List Int)} {P : Nat → Nat} {R c : Nat} {r : Equiv.Perm (Fin 22)}
    (hr : imageList r = (unpack 22 5 R).toList)
    (hg : ∀ j < (ws.map (evalCodes [m22gA, m22gB])).length,
      imageList ((ws.map (evalCodes [m22gA, m22gB])).getD j 1) = (unpack 22 5 (P j)).toList)
    (hc : ws.length = c) (hk : allN c (fun j => commK 22 5 (mask 5) (22 * 5) (P j) R) = true) :
    (ws.map (evalCodes [m22gA, m22gB])).all (fun h => commT 22 (toTable h) (toTable r)) =
      true := by
  rw [List.all_eq_true]
  intro h hh
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hh
  have himg := hg j hj
  rw [List.getD_eq_getElem _ _ hj] at himg
  exact commT_of_commK himg hr (allN_spec hk j (by simpa [hc] using hj))

theorem cent1 : m22CentQ1.check = true ∧ m22CentQ1.orderCertificate = 384 ∧
      (m22CentWords1.map (evalCodes [m22gA, m22gB])).all
        (fun h => commT 22 (toTable h) (toTable ((m22InvReps).getD 0 1))) = true ∧
      oddWitnessOK 22 3 (allTables m22CentQ1) = true := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainC1
  exact ⟨h1, h2.trans (by decide), comm_of imgRep0 chainC1.2.2.2.1 (by decide) commC1,
    chainK_odd (by decide) (by decide) chainC1 M22O1.ok⟩

theorem y0hc : Counts2 M22Q.LR M22Y0.CS (cntWord2K 22 5 (mask 5) (22 * 5) (pidn 22 5) M22Q.LR M22Q.TR
    5 2 4 m22AutWords R0) := by
  rw [← cntWord2F_eq (by norm_num) (by norm_num)]
  exact M22Y0.hc

theorem aut : ordTest 22 2 (toTable m22gA) = true ∧ ordTest 22 4 (toTable m22gB) = true ∧
      wordsTest 22 2 4 m22AutWords (toTable m22gA) (toTable m22gB) = true ∧
      repsTotal 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (m22InvReps.map toTable) (orderTables m22Certificate 4) 2000
        (wordsTest 22 2 4 m22AutWords) = 887040 := by
  refine ⟨ordTest_of_ordIs szOK' imgA cA (by norm_num) ordA,
    ordTest_of_ordIs szOK' imgB cB (by norm_num) ordB,
    wordsTest_of_wordOrdK szOK' imgA imgB wordsAB, ?_⟩
  have h := chainK_repsTotal3 (mx := 2) (my := 4) (by decide) (by decide) chainQ tA_eq tB_eq
    (by norm_num) clsOK2 hR (by norm_num) (by norm_num) (CW := [M22Y0.CS])
    ⟨rfl, fun j hj => by
      have hj1 : j < 1 := by simpa [M22CK] using hj
      interval_cases j
      exact y0hc⟩
  exact h.trans (by decide)

theorem facts : (repsOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (cosetOrderTables m22Certificate 1 2) (m22InvReps.map toTable) 2000 = true ∧
      repSizes 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (m22InvReps.map toTable) 2000 = [1155] ∧
      (m22InvReps.map toTable).all (ordTest 22 2) = true
    )
    ∧ (m22CentQ1.check = true ∧ m22CentQ1.orderCertificate = 384 ∧
      (m22CentWords1.map (evalCodes [m22gA, m22gB])).all
        (fun h => commT 22 (toTable h) (toTable ((m22InvReps).getD 0 1))) = true ∧
      oddWitnessOK 22 3 (allTables m22CentQ1) = true
    )
    ∧ (ordTest 22 2 (toTable m22gA) = true ∧ ordTest 22 4 (toTable m22gB) = true ∧
      wordsTest 22 2 4 m22AutWords (toTable m22gA) (toTable m22gB) = true ∧
      repsTotal 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (m22InvReps.map toTable) (orderTables m22Certificate 4) 2000 (wordsTest 22 2 4 m22AutWords) =
          887040
    ) := ⟨cover, cent1, aut⟩

end CertificateChecks.KernelSporSch.M22OC

end
