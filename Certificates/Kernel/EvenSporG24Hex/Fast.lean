module

public import Certificates.Data.Kernel.EvenSporG24Hex.Defs

public section

namespace CertificateChecks.KernelG24Hex

open CFSG.KC.EvenSporG24Hex

@[expose] def allL2 (f : Nat → Nat → Bool) : Nat → List Nat → List Nat → Bool
  | 0, _, _ => true
  | n + 1, u :: us, w :: ws => f u w && allL2 f n us ws
  | n + 1, U, W => (List.range (n + 1)).all fun k => f (U.getD k 0) (W.getD k 0)

@[expose] def allL3 (f : Nat → Nat → Nat → Bool) : Nat → List Nat → List Nat → List Nat → Bool
  | 0, _, _, _ => true
  | n + 1, u :: us, w :: ws, p :: ps => f u w p && allL3 f n us ws ps
  | n + 1, U, W, P => (List.range (n + 1)).all fun k => f (U.getD k 0) (W.getD k 0) (P.getD k 0)

@[expose] def mapL2 (f : Nat → Nat → Nat) : Nat → List Nat → List Nat → List Nat
  | 0, _, _ => []
  | n + 1, u :: us, w :: ws => f u w :: mapL2 f n us ws
  | n + 1, U, W => (List.range (n + 1)).map fun k => f (U.getD k 0) (W.getD k 0)

theorem allL2_eq (f : Nat → Nat → Bool) : ∀ (n : Nat) (U W : List Nat),
    allL2 f n U W = (List.range n).all fun k => f (U.getD k 0) (W.getD k 0)
  | 0, _, _ => rfl
  | n + 1, u :: us, w :: ws => by
    rw [allL2, allL2_eq f n us ws, List.range_succ_eq_map, List.all_cons, List.all_map]
    rfl
  | _ + 1, [], _ => rfl
  | _ + 1, _ :: _, [] => rfl

theorem allL3_eq (f : Nat → Nat → Nat → Bool) : ∀ (n : Nat) (U W P : List Nat),
    allL3 f n U W P = (List.range n).all fun k => f (U.getD k 0) (W.getD k 0) (P.getD k 0)
  | 0, _, _, _ => rfl
  | n + 1, u :: us, w :: ws, p :: ps => by
    rw [allL3, allL3_eq f n us ws ps, List.range_succ_eq_map, List.all_cons, List.all_map]
    rfl
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, [], _ => rfl
  | _ + 1, _ :: _, _ :: _, [] => rfl

theorem mapL2_eq (f : Nat → Nat → Nat) : ∀ (n : Nat) (U W : List Nat),
    mapL2 f n U W = (List.range n).map fun k => f (U.getD k 0) (W.getD k 0)
  | 0, _, _ => rfl
  | n + 1, u :: us, w :: ws => by
    rw [mapL2, mapL2_eq f n us ws, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  | _ + 1, [], _ => rfl
  | _ + 1, _ :: _, [] => rfl

theorem linesOK_eq (U W : List Nat) : linesOK U W =
    allL2 (fun u w => strictInc (isortN (codesK u w)) && (isortN (codesK u w)).all (· != 0))
      1365 U W := by
  rw [allL2_eq]
  rfl

theorem keysOK_eq (U W : List Nat) : keysOK U W =
    strictInc (isortN (mapL2 (fun u w => pk 28 (isortN (codesK u w))) 1365 U W)) := by
  rw [mapL2_eq]
  rfl

theorem lcOK_eq (U W : List Nat) (LC : Nat) : lcOK U W LC =
    (LC == pk 420 (mapL2 (fun u w => pk 28 (codesK u w)) 1365 U W)) := by
  rw [mapL2_eq]
  rfl

theorem hexJ_eq (U W : List Nat) (GE PG : List (List Nat)) (LC j : Nat) :
    hexJ U W GE PG LC j =
      allL3 (fun u w p => memP (mulP (pk 28 (csOf (GE.getD j []))) u) (fld 420 LC (p % 1365)) &&
          memP (mulP (pk 28 (csOf (GE.getD j []))) w) (fld 420 LC (p % 1365)))
        1365 U W (PG.getD j []) := by
  rw [allL3_eq]
  rfl

end CertificateChecks.KernelG24Hex

end
