module

public import Certificates.Kernel.SporSch.Ly.CoverData
public import Certificates.Kernel.SporSch.Ly.BS18009
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyCvF

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF CertificateChecks.KernelSporSch.LyCv

local notation "U" X:max => unpackL 111 12 1332 X

noncomputable abbrev CS : Array (Mat × Mat) := cStarArr (U B4)

theorem extend_size : ∀ (ws : List (List Int)) (acc : Array (Mat × Mat)),
    (extendM acc ws).size = acc.size + ws.length
  | [], _ => rfl
  | w :: vs, acc => by
    have e : extendM acc (w :: vs) = extendM (acc.push
        (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w,
          invM 5 111 (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w))) vs :=
      rfl
    rw [e, extend_size vs, Array.size_push, List.length_cons]
    omega

theorem cs_size : CS.size = 12 := by
  unfold CS cStarArr
  rw [extend_size]
  rfl

theorem cs_get {i : Nat} (hi : i < CS.size) : CS[i] = (U (CFx 12 i), U (CIx 12 i)) := by
  have e : CS[i] = pairAt CS i := by
    unfold pairAt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  rw [e, ← csCF, ← csCI]

theorem invPairs : invPairsOK CS = true := by
  unfold invPairsOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 12 := by rw [← cs_size]; exact hi
  have e := cs_get hi
  have ef : CFx 12 i = CF i ∧ CIx 12 i = CI i := by
    unfold CFx CIx
    rw [bl hi']
    exact ⟨rfl, rfl⟩
  rw [ef.1, ef.2] at e
  rw [e]
  dsimp only
  rw [mulE (vCFi hi').1 (vCFi hi').2, idE, beqE (mulV (vCFi hi').1 (vCFi hi').2) vOne]
  exact allN_spec iCF i hi'

theorem cf0 : (pairAt CS 0).1 = U (CF 0) := by
  rw [csCF]
  unfold CFx
  rw [bl (by norm_num)]

theorem cf1 : (pairAt CS 1).1 = U (CF 1) := by
  rw [csCF]
  unfold CFx
  rw [bl (by norm_num)]

open CFSG.Sporadic.LySchreier (carPresOK carMat oneOrA carFoldM carGenWords carWords)

theorem carYE (i : Fin 9) : carMat CS i = U (carYK i.val) ∧ vld (carYK i.val) = true :=
  word_of csCF csCI (fun i => (vCFx le_rfl i).1) (fun i => (vCFx le_rfl i).2) (carWords i)

theorem oneOrAE {X : Nat} (hX : vld X = true) : oneOrA (U X) = oneOrAK X := by
  unfold oneOrA oneOrAK
  rw [idE, matA_eq, beqE hX vOne, beqE hX vA]
  cases Nat.beq X ONE <;> rfl

theorem foldYE : ∀ (w : List (Fin 9)) (X : Nat), vld X = true →
    w.foldl (fun M n => mulM 5 111 M (carMat CS n)) (U X) =
      U (w.foldl (fun X n => mul X (carYK n.val)) X) ∧
      vld (w.foldl (fun X n => mul X (carYK n.val)) X) = true
  | [], _, hX => ⟨rfl, hX⟩
  | n :: w, X, hX => by
    simp only [List.foldl_cons]
    rw [(carYE n).1, mulE hX (carYE n).2]
    exact foldYE w _ (mulV hX (carYE n).2)

theorem carFoldE (w : List (Fin 9)) : carFoldM (carMat CS) w = U (carFoldK w) := by
  unfold carFoldM carFoldK
  rw [idE]
  exact (foldYE w ONE vOne).1

theorem carPairs (i j : Nat) (hi : i < 8) (hj : j < 9) : carPairK i j = true := by
  interval_cases i
  exacts [allN_spec carP0 j hj, allN_spec carP1 j hj, allN_spec carP2 j hj,
    allN_spec carP3 j hj, allN_spec carP4 j hj, allN_spec carP5 j hj, allN_spec carP6 j hj,
    allN_spec carP7 j hj]

theorem carPres : carPresOK CS = true := by
  unfold carPresOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const]
  refine ⟨⟨⟨fun i => ?_, fun i j => ?_⟩, fun k => ?_⟩, ?_⟩
  · have v := (carYE i).2
    rw [(carYE i).1, mulE v v, mulE (mulV v v) v, oneOrAE (mulV (mulV v v) v)]
    exact allN_spec carCube i.val i.isLt
  · by_cases h : i < j
    · have vi := (carYE i).2
      have vj := (carYE j).2
      have vp := mulV vi vj
      rw [(carYE i).1, (carYE j).1, mulE vi vj, mulE vp vp, oneOrAE (mulV vp vp), Bool.or_eq_true]
      right
      have h' : i.val < j.val := h
      have hp := carPairs i.val j.val (by omega) j.isLt
      unfold carPairK at hp
      rw [bl h'] at hp
      exact hp
    · simp [h]
  · have v0 := (vCFi (i := 0) (by norm_num)).1
    fin_cases k
    · change (carFoldM (carMat CS) (carGenWords 0) == (pairAt CS 0).1 ||
        carFoldM (carMat CS) (carGenWords 0) == mulM 5 111 (pairAt CS 0).1 matA) = true
      rw [carFoldE, cf0, matA_eq, mulE v0 vA, Nat.eq_of_beq_eq_true carG0]
      simp
    · change (carFoldM (carMat CS) (carGenWords 1) == (pairAt CS 1).1 ||
        carFoldM (carMat CS) (carGenWords 1) == mulM 5 111 (pairAt CS 1).1 matA) = true
      rw [carFoldE, cf1, Nat.eq_of_beq_eq_true carG1]
      simp
  · have v0 := (carYE 0).2
    have v1 := (carYE 1).2
    have vp := mulV v0 v1
    rw [(carYE 0).1, (carYE 1).1, mulE v0 v1, mulE vp vp, matA_eq, beqE (mulV vp vp) vA]
    exact carZ

theorem facts : coverCertificate () = true := by
  unfold coverCertificate
  simp only []
  rw [b4_eq]
  have v0 := (vCFi (i := 0) (by norm_num)).1
  have v1 := (vCFi (i := 1) (by norm_num)).1
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, invPairs⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, carPres⟩
  · rw [matB_eq, mulE vB vB4, idE, beqE (mulV vB vB4) vOne]
    exact bB
  · rw [cs_size]
    rfl
  · rw [cf0, matA_eq, mulE vA v0, mulE v0 vA, beqE (mulV vA v0) (mulV v0 vA)]
    exact c0A
  · rw [cf1, matA_eq, mulE vA v1, mulE v1 vA, beqE (mulV vA v1) (mulV v1 vA)]
    exact c1A
  · rw [cf0, idE, diffMod5_eq consts (hv v0) (hv vOne)]
    exact c0n1
  · rw [cf0, matA_eq, diffMod5_eq consts (hv v0) (hv vA)]
    exact c0nA

end CertificateChecks.KernelSporSch.LyCvF

end
