module

public import Certificates.Kernel.E6Heart.Data
import all Certificates.Data.E6Heart

public section

namespace CertificateChecks.E6HeartK

open Certificates.E6Heart

@[expose] noncomputable def nthN (P : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih i => Nat.rec (motive := fun _ => Nat) p (fun j _ => ih j) i) P

@[expose] def bitN (m j : Nat) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 j))

@[expose] noncomputable def adjK (i j : Nat) : Bool :=
  Bool.rec (adjB i j) (bitN (nthN adjT i) j) (Nat.blt i 72 && Nat.blt j 72)

@[expose] noncomputable def zK (i t : Nat) : Bool :=
  Bool.rec (pair3 (rootAt i) (repL t) == 0) (bitN (nthN zT i) t) (Nat.blt i 72 && Nat.blt t 243)

@[expose] noncomputable def adjOk : Bool :=
  (List.range 72).all fun i => (List.range 72).all fun j => adjB i j == bitN (nthN adjT i) j

@[expose] noncomputable def zOk : Bool :=
  (List.range 72).all fun i => (List.range 243).all fun t =>
    (pair3 (rootAt i) (repL t) == 0) == bitN (nthN zT i) t

@[expose] noncomputable def phiLK (t : Nat) : List Nat := (List.range 72).filter (fun i => zK i t)

@[expose] noncomputable def stepLK (pm seen : List Nat) : List Nat :=
  seen ++ pm.filter (fun j => !seen.contains j && seen.any (fun i => adjK i j))

@[expose] noncomputable def iterStepK (pm : List Nat) : Nat → List Nat → List Nat
  | 0, seen => seen
  | k + 1, seen =>
    let next := stepLK pm seen
    if next.length == seen.length then seen else iterStepK pm k next

@[expose] noncomputable def compOfK (pm : List Nat) (seed : Nat) : List Nat := iterStepK pm 72 [seed]

@[expose] noncomputable def closedInK (pm c : List Nat) : Bool :=
  pm.all (fun j => c.contains j || !c.any (fun i => adjK i j))

@[expose] noncomputable def kerSizeK (c : List Nat) : Nat :=
  ((List.range 243).filter (fun t => c.all (fun i => zK i t))).length

@[expose] noncomputable def goodAtK (t : Nat) : Bool :=
  let pm := phiLK t
  let q := qOf (repL t)
  let ps := pm.map (fun i => (i, compOfK pm i))
  ps.all (fun p => closedInK pm p.2) &&
    (if q == 0 then ps.all (fun p => p.2.length ≤ 6)
     else
      ps.all (fun p => p.2.length ≤ 6 ||
          ps.all (fun r => r.2.length ≤ 6 || p.2.contains r.1)) &&
        ps.any (fun p => p.2.length == (if q == 1 then 24 else 30) && kerSizeK p.2 == 3))

@[expose] noncomputable def checkK : Bool :=
  rootsOk () && radOk () && (List.range 243).all (fun t => t == 0 || goodAtK t) &&
    cntQ 0 == 80 && cntQ 1 == 90 && cntQ 2 == 72

section

variable (hA : adjOk = true) (hZ : zOk = true)

include hA in
theorem adjB_eq (i j : Nat) : adjB i j = adjK i j := by
  unfold adjK
  cases hc : (Nat.blt i 72 && Nat.blt j 72)
  · rfl
  · rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hc
    have h1 := List.all_eq_true.1 hA i (List.mem_range.2 hc.1)
    exact beq_iff_eq.1 (List.all_eq_true.1 h1 j (List.mem_range.2 hc.2))

include hZ in
theorem z_eq (i t : Nat) : (pair3 (rootAt i) (repL t) == 0) = zK i t := by
  unfold zK
  cases hc : (Nat.blt i 72 && Nat.blt t 243)
  · rfl
  · rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hc
    have h1 := List.all_eq_true.1 hZ i (List.mem_range.2 hc.1)
    exact beq_iff_eq.1 (List.all_eq_true.1 h1 t (List.mem_range.2 hc.2))

include hA in
theorem iterStep_eq (pm : List Nat) : ∀ k seen, iterStep pm k seen = iterStepK pm k seen
  | 0, _ => rfl
  | k + 1, seen => by
    have e : stepL pm seen = stepLK pm seen := by simp only [stepL, stepLK, adjB_eq hA]
    simp only [iterStep, iterStepK, e, iterStep_eq pm k]

include hA hZ in
theorem goodAt_eq (t : Nat) : goodAt t = goodAtK t := by
  have hc : ∀ pm i, compOf pm i = compOfK pm i := fun pm i => iterStep_eq hA pm 72 [i]
  have hp : phiL (repL t) = phiLK t := by simp only [phiL, phiLK, z_eq hZ]
  have hk : ∀ c, kerSize c = kerSizeK c := fun c => by simp only [kerSize, kerSizeK, z_eq hZ]
  have hcl : ∀ pm c, closedIn pm c = closedInK pm c := fun pm c => by
    simp only [closedIn, closedInK, adjB_eq hA]
  simp only [goodAt, goodAtK, hc, hp, hk, hcl]

include hA hZ in
theorem check_eq : check () = checkK := by
  simp only [check, checkK, goodAt_eq hA hZ]

end

end CertificateChecks.E6HeartK
