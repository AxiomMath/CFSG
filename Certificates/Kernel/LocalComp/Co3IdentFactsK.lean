
module

public import Certificates.Kernel.LocalComp.Co3IdentElts
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentFactsInputs
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Co3Bfs
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Co3.Native CertificateChecks.KernelLC CertificateChecks.KernelSpor

theorem kRels : relsV.all (fun r => bAnd(wordOK r, Nat.beq (wordP r) (pidn 276 9))) = true := by
  quickRfl

theorem rels : relsV.all (fun r => eqA 276 (wordArr r) (idA 276)) = true := by
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (List.all_eq_true.1 kRels r hr)
  rw [wordArr_eq r h1, eqA_idA (wordP_canon r h1), h2]

theorem kC32 : Nat.beq (pc P3 P2) (pc P2 P3) = true := by quickRfl
theorem kC35 : Nat.beq (pc P3 P5) (pc P5 P3) = true := by quickRfl
theorem kN04 : (!Nat.beq P0 P4) = true := by quickRfl
theorem kN0 : (!Nat.beq P0 (pidn 276 9)) = true := by quickRfl
theorem kS0 : Nat.beq (pc P0 P0) (pidn 276 9) = true := by quickRfl

@[expose] noncomputable def cenOK (j : Nat) : Bool :=
  !(Nat.beq (pc (HR.E j) (HR.G 0)) (pc (HR.G 0) (HR.E j)) &&
      Nat.beq (pc (HR.E j) (HR.G 1)) (pc (HR.G 1) (HR.E j)) &&
      Nat.beq (pc (HR.E j) (HR.G 2)) (pc (HR.G 2) (HR.E j))) ||
    (Nat.beq (HR.E j) (pidn 276 9) || Nat.beq (HR.E j) P4 || Nat.beq (HR.E j) P0 ||
      Nat.beq (HR.E j) EAP)

theorem kCen0 : allFrom (256 * 0) 256 cenOK = true := by quickRfl
theorem kCen1 : allFrom (256 * 1) 256 cenOK = true := by quickRfl
theorem kCen2 : allFrom (256 * 2) 256 cenOK = true := by quickRfl
theorem kCen3 : allFrom (256 * 3) 256 cenOK = true := by quickRfl
theorem kCen4 : allFrom (256 * 4) 256 cenOK = true := by quickRfl
theorem kCen5 : allFrom (256 * 5) 256 cenOK = true := by quickRfl
theorem kCen6 : allFrom (256 * 6) 256 cenOK = true := by quickRfl
theorem kCen7 : allFrom (256 * 7) 256 cenOK = true := by quickRfl
theorem kCen8 : allFrom (256 * 8) 256 cenOK = true := by quickRfl
theorem kCen9 : allFrom (256 * 9) 256 cenOK = true := by quickRfl
theorem kCen10 : allFrom (256 * 10) 256 cenOK = true := by quickRfl
theorem kCen11 : allFrom (256 * 11) 256 cenOK = true := by quickRfl
theorem kCen12 : allFrom (256 * 12) 256 cenOK = true := by quickRfl
theorem kCen13 : allFrom (256 * 13) 256 cenOK = true := by quickRfl
theorem kCen14 : allFrom (256 * 14) 256 cenOK = true := by quickRfl
theorem kCen15 : allFrom (256 * 15) 256 cenOK = true := by quickRfl
theorem kCen16 : allFrom (256 * 16) 256 cenOK = true := by quickRfl
theorem kCen17 : allFrom (256 * 17) 256 cenOK = true := by quickRfl

theorem cenOK_all (j : Nat) (hj : j < 4608) : cenOK j = true := by
  refine blocks (B := 256) (nb := 18) (by omega) (fun k hk => ?_) j (by omega)
  interval_cases k
  · exact kCen0
  · exact kCen1
  · exact kCen2
  · exact kCen3
  · exact kCen4
  · exact kCen5
  · exact kCen6
  · exact kCen7
  · exact kCen8
  · exact kCen9
  · exact kCen10
  · exact kCen11
  · exact kCen12
  · exact kCen13
  · exact kCen14
  · exact kCen15
  · exact kCen16
  · exact kCen17

theorem cen (j : Nat) (hj : j < 4608) :
    (commutesA 276 hList[j]! gArrs[0]! && commutesA 276 hList[j]! gArrs[1]! &&
      commutesA 276 hList[j]! gArrs[2]!) = true →
    (eqA 276 hList[j]! (idA 276) || eqA 276 hList[j]! (genArr 4) ||
      eqA 276 hList[j]! (genArr 0) || eqA 276 hList[j]! eaArr) = true := by
  have h := cenOK_all j hj
  have cj := cHR j hj
  unfold cenOK at h
  rw [hList_get j hj, g_eq 0 (by omega), g_eq 1 (by omega), g_eq 2 (by omega),
    comm_unpack cj (cG 0 (by omega)), comm_unpack cj (cG 1 (by omega)),
    comm_unpack cj (cG 2 (by omega)), eqA_idA cj, bind4, bind0, ea_eq, eqA_unpack cj c4,
    eqA_unpack cj c0, eqA_unpack cj cEA]
  intro hc'
  rw [hc'] at h
  simpa using h

@[expose] noncomputable def cy (X : Nat) : Bool := Nat.beq (pc X YP) (pc YP X)

theorem kCnt0 : Nat.beq ((List.range 512).filter fun d => cy (HR.E (512 * 0 + d))).length 14
    = true := by quickRfl
theorem kCnt1 : Nat.beq ((List.range 512).filter fun d => cy (HR.E (512 * 1 + d))).length 8
    = true := by quickRfl
theorem kCnt2 : Nat.beq ((List.range 512).filter fun d => cy (HR.E (512 * 2 + d))).length 9
    = true := by quickRfl
theorem kCnt3 : Nat.beq ((List.range 512).filter fun d => cy (HR.E (512 * 3 + d))).length 10
    = true := by quickRfl
theorem kCnt4 : Nat.beq ((List.range 512).filter fun d => cy (HR.E (512 * 4 + d))).length 13
    = true := by quickRfl
theorem kCnt5 : Nat.beq ((List.range 512).filter fun d => cy (HR.E (512 * 5 + d))).length 13
    = true := by quickRfl
theorem kCnt6 : Nat.beq ((List.range 512).filter fun d => cy (HR.E (512 * 6 + d))).length 19
    = true := by quickRfl
theorem kCnt7 : Nat.beq ((List.range 512).filter fun d => cy (HR.E (512 * 7 + d))).length 19
    = true := by quickRfl
theorem kCnt8 : Nat.beq ((List.range 512).filter fun d => cy (HR.E (512 * 8 + d))).length 23
    = true := by quickRfl

theorem filter_succ (p : Nat → Bool) (B n : Nat) :
    ((List.range (B * (n + 1))).filter p).length =
      ((List.range (B * n)).filter p).length + ((List.range B).filter fun d => p (B * n + d)).length := by
  rw [Nat.mul_succ, List.range_add, List.filter_append, List.length_append, List.filter_map,
    List.length_map]
  rfl

theorem cnt : ((List.range 4608).filter fun j => commutesA 276 hList[j]! yArr).length = 128 := by
  have e : ((List.range 4608).filter fun j => commutesA 276 hList[j]! yArr) =
      (List.range 4608).filter fun j => cy (HR.E j) := by
    refine List.filter_congr fun j hj => ?_
    have hj' := List.mem_range.1 hj
    rw [hList_get j hj', y_eq, comm_unpack (cHR j hj') cY]
    rfl
  rw [e]
  have h : ((List.range (512 * 9)).filter fun j => cy (HR.E j)).length = 128 := by
    rw [filter_succ, filter_succ, filter_succ, filter_succ, filter_succ, filter_succ, filter_succ,
      filter_succ, filter_succ, Nat.eq_of_beq_eq_true kCnt0, Nat.eq_of_beq_eq_true kCnt1,
      Nat.eq_of_beq_eq_true kCnt2, Nat.eq_of_beq_eq_true kCnt3, Nat.eq_of_beq_eq_true kCnt4,
      Nat.eq_of_beq_eq_true kCnt5, Nat.eq_of_beq_eq_true kCnt6, Nat.eq_of_beq_eq_true kCnt7,
      Nat.eq_of_beq_eq_true kCnt8]
    rfl
  exact h

theorem kEdge2 : allN 6 (fun k => bAnd(wordOK (pos (edgePairs.getD k ([], [])).1),
    bAnd(wordOK (pos (edgePairs.getD k ([], [])).2),
      Nat.beq (pc P3 (pc (wordP (pos (edgePairs.getD k ([], [])).1)) P3))
        (wordP (pos (edgePairs.getD k ([], [])).2))))) = true := by quickRfl

theorem edges (k : Nat) (hk : k < 6) :
    eqA 276 (compA 276 (genArr 3) (compA 276 (posArr (edgePairs.getD k ([], [])).1)
      (genArr 3))) (posArr (edgePairs.getD k ([], [])).2) = true := by
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 (allN_spec kEdge2 k hk)
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  unfold posArr
  rw [wordArr_eq _ h1, wordArr_eq _ h2, bind3, compA_unpack (wordP_canon _ h1) c3,
    compA_unpack c3 (canon_pc (wordP_canon _ h1) c3),
    eqA_unpack (canon_pc c3 (canon_pc (wordP_canon _ h1) c3)) (wordP_canon _ h2)]
  exact h3

theorem kBc1 : Nat.beq (pc BCBP BCBP) (pidn 276 9) = true := by quickRfl
theorem kBc2 : Nat.beq (pc BCBP (pc P0 BCBP)) YP = true := by quickRfl
theorem kBc3 : Nat.beq (pc BCBP (pc YP BCBP)) P0 = true := by quickRfl
theorem kBc4 : Nat.beq (pc BCBP (pc P2 BCBP)) P2 = true := by quickRfl
theorem kK1 : Nat.beq (pc KPP P0) (pc P0 KPP) = true := by quickRfl
theorem kK2 : Nat.beq (pc KPP YP) (pc YP KPP) = true := by quickRfl
theorem kK3 : Nat.beq (pc KPP KPP) (pidn 276 9) = true := by quickRfl
theorem kK4 : (!Nat.beq KPP (pidn 276 9)) = true := by quickRfl
theorem kU3 : Nat.beq (pc UP (pc UP UP)) KPP = true := by quickRfl
theorem kEA10 : Nat.beq (CR.E 10) EAP = true := by quickRfl

theorem facts3094 : relsV.all (fun r => eqA 276 (wordArr r) (idA 276)) = true ∧
      commutesA 276 (genArr 3) (genArr 2) = true ∧ commutesA 276 (genArr 3) (genArr 5) = true ∧
      eqA 276 (genArr 0) (genArr 4) = false ∧ eqA 276 (genArr 0) (idA 276) = false ∧
      eqA 276 (compA 276 (genArr 0) (genArr 0)) (idA 276) = true ∧
      (∀ j < 4608, (commutesA 276 hList[j]! gArrs[0]! && commutesA 276 hList[j]! gArrs[1]! &&
        commutesA 276 hList[j]! gArrs[2]!) = true →
        (eqA 276 hList[j]! (idA 276) || eqA 276 hList[j]! (genArr 4) ||
          eqA 276 hList[j]! (genArr 0) || eqA 276 hList[j]! eaArr) = true) ∧
      ((List.range 4608).filter fun j => commutesA 276 hList[j]! yArr).length = 128 ∧
      (∀ k < 6, eqA 276 (compA 276 (genArr 3) (compA 276 (posArr (edgePairs.getD k ([], [])).1)
        (genArr 3))) (posArr (edgePairs.getD k ([], [])).2) = true) ∧
      eqA 276 (compA 276 bcbArr bcbArr) (idA 276) = true ∧
      eqA 276 (compA 276 bcbArr (compA 276 (genArr 0) bcbArr)) yArr = true ∧
      eqA 276 (compA 276 bcbArr (compA 276 yArr bcbArr)) (genArr 0) = true ∧
      eqA 276 (compA 276 bcbArr (compA 276 (genArr 2) bcbArr)) (genArr 2) = true ∧
      commutesA 276 kpArr (genArr 0) = true ∧ commutesA 276 kpArr yArr = true ∧
      eqA 276 (compA 276 kpArr kpArr) (idA 276) = true ∧ eqA 276 kpArr (idA 276) = false ∧
      eqA 276 (compA 276 uArr (compA 276 uArr uArr)) kpArr = true ∧
      ((List.range 630).any fun j => eqA 276 cBFS.1[j]! eaArr) = true := by
  refine ⟨rels, ?_, ?_, ?_, ?_, ?_, cen, cnt, edges, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bind3, bind2, comm_unpack c3 c2]
    exact kC32
  · rw [bind3, bind5, comm_unpack c3 c5]
    exact kC35
  · rw [bind0, bind4, eqA_unpack c0 c4]
    simpa using kN04
  · rw [bind0, eqA_idA c0]
    simpa using kN0
  · rw [bind0, compA_unpack c0 c0, eqA_idA (canon_pc c0 c0)]
    exact kS0
  · rw [bcb_eq, compA_unpack cBCB cBCB, eqA_idA (canon_pc cBCB cBCB)]
    exact kBc1
  · rw [bcb_eq, bind0, y_eq, compA_unpack c0 cBCB, compA_unpack cBCB (canon_pc c0 cBCB),
      eqA_unpack (canon_pc cBCB (canon_pc c0 cBCB)) cY]
    exact kBc2
  · rw [bcb_eq, bind0, y_eq, compA_unpack cY cBCB, compA_unpack cBCB (canon_pc cY cBCB),
      eqA_unpack (canon_pc cBCB (canon_pc cY cBCB)) c0]
    exact kBc3
  · rw [bcb_eq, bind2, compA_unpack c2 cBCB, compA_unpack cBCB (canon_pc c2 cBCB),
      eqA_unpack (canon_pc cBCB (canon_pc c2 cBCB)) c2]
    exact kBc4
  · rw [kp_eq, bind0, comm_unpack cKP c0]
    exact kK1
  · rw [kp_eq, y_eq, comm_unpack cKP cY]
    exact kK2
  · rw [kp_eq, compA_unpack cKP cKP, eqA_idA (canon_pc cKP cKP)]
    exact kK3
  · rw [kp_eq, eqA_idA cKP]
    simpa using kK4
  · rw [u_eq, kp_eq, compA_unpack cU cU, compA_unpack cU (canon_pc cU cU),
      eqA_unpack (canon_pc cU (canon_pc cU cU)) cKP]
    exact kU3
  · rw [List.any_eq_true]
    refine ⟨10, List.mem_range.2 (by omega), ?_⟩
    rw [cList_get 10 (by omega), ea_eq, eqA_unpack (cCR 10 (by omega)) cEA]
    exact kEA10

end CertificateChecks.KernelLC.Co3Id

end
