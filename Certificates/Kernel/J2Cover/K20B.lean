
module

public import Certificates.Kernel.J2Cover.K20A
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText TxtExternal
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.External

noncomputable abbrev φ (X : Nat) : Table := arrTable 315 (unpack 315 9 X)

theorem ordT_of {m X : Nat} (hm : 0 < m) (c : CnN 315 9 X) :
    ordTest 315 m (φ X) = ordPK 315 9 m (prodK 315 9 [X]) := by
  unfold ordTest
  exact ordW_unpack (ws := [X]) hm fun Y hY => by rw [List.mem_singleton.1 hY]; exact c

@[expose] noncomputable def f2K (X : Nat) : Bool := ordPK 315 9 2 (prodK 315 9 [X])

@[expose] noncomputable def f3K (X : Nat) : Bool := ordPK 315 9 3 (prodK 315 9 [X])

@[expose] noncomputable def L2 : List Nat := prodList 315 9 1 FD.LR FD.TR f2K

@[expose] noncomputable def L3 : List Nat := prodList 315 9 1 FD.LR FD.TR f3K

theorem hd2 : dOrderTables 2 = L2.map φ ∧ ∀ X ∈ L2, CnN 315 9 X := by
  unfold dOrderTables
  exact prodList_sound fD_binds fD_perm FD.hl fun X c => ordT_of (by norm_num) c

theorem hd3 : dOrderTables 3 = L3.map φ ∧ ∀ X ∈ L3, CnN 315 9 X := by
  unfold dOrderTables
  exact prodList_sound fD_binds fD_perm FD.hl fun X c => ordT_of (by norm_num) c

@[expose] noncomputable def r7K (X Y : Nat) : Bool := ordPK 315 9 7 (prodK 315 9 [X, Y])

@[expose] noncomputable def r74K (X Y : Nat) : Bool :=
  bAnd(ordPK 315 9 7 (prodK 315 9 [X, Y]), ordPK 315 9 4 (prodK 315 9 [X, Y, X, Y, Y]))

theorem pc1K : Nat.beq (pairCntK L2 L3 r7K) 336 = true := by quickRfl

theorem pc2K : Nat.beq (pairCntK L2 L3 r74K) 336 = true := by quickRfl

theorem len2K : Nat.beq (lenL L2) 21 = true := by quickRfl

theorem fix2K : allL (fun X => Nat.beq (fixK 315 9 X) 11) L2 = true := by quickRfl

theorem lenL_eq : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenL_eq L)

theorem canon2 {X Y : Nat} (cX : CnN 315 9 X) (cY : CnN 315 9 Y) : ∀ Z ∈ [X, Y], CnN 315 9 Z := by
  intro Z hZ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ
  rcases hZ with rfl | rfl <;> assumption

theorem pairT_of {X Y : Nat} (cX : CnN 315 9 X) (cY : CnN 315 9 Y) :
    pairTest 315 7 4 2 3 (φ X) (φ Y) = r74K X Y := by
  have hc : ∀ Z ∈ [X, Y, X, Y, Y], CnN 315 9 Z := by
    intro Z hZ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ
    rcases hZ with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h1 := ordW_unpack (n := 315) (w := 9) (m := 7) (ws := [X, Y]) (by norm_num) (canon2 cX cY)
  have h2 := ordW_unpack (n := 315) (w := 9) (m := 4) (ws := [X, Y, X, Y, Y]) (by norm_num) hc
  unfold pairTest r74K
  rw [← h1, ← h2]
  rfl

@[expose] noncomputable def cmK (E : Nat) : Bool :=
  bAnd(Nat.beq (pcomp 315 9 (mask 9) E (FD.S 0)) (pcomp 315 9 (mask 9) (FD.S 0) E),
    Nat.beq (pcomp 315 9 (mask 9) E (FD.S 1)) (pcomp 315 9 (mask 9) (FD.S 1) E))

theorem cntCK : Nat.beq (prodCnt 315 9 2 FC.LR FC.TR cmK) 1 = true := by quickRfl

theorem tableC : tableCheck = true := by
  have c0 : CnN 315 9 (FD.S 0) := by quickRfl
  have c1 : CnN 315 9 (FD.S 1) := by quickRfl
  have hX : tblX = φ (FD.S 0) := by unfold tblX; rw [fD_S 0 (by omega)]
  have hY : tblY = φ (FD.S 1) := by unfold tblY; rw [fD_S 1 (by omega)]
  have o2 : ordTest 315 2 tblX = true := by rw [hX, ordT_of (by norm_num) c0]; quickRfl
  have o3 : ordTest 315 3 tblY = true := by rw [hY, ordT_of (by norm_num) c1]; quickRfl
  have pt : pairTest 315 7 4 2 3 tblX tblY = true := by rw [hX, hY, pairT_of c0 c1]; quickRfl
  have l2 : ((dOrderTables 2).length == 21) = true := by
    rw [hd2.1, List.length_map, ← lenL_eq, Nat.eq_of_beq_eq_true len2K]
    rfl
  have a2 : (dOrderTables 2).all (fun T => tblFix T == 11) = true := by
    rw [hd2.1, List.all_map, List.all_eq_true]
    intro X hX
    have h := allL_spec fix2K X hX
    simp only [Function.comp_apply]
    rw [tblFix_unpack (hd2.2 X hX), Nat.eq_of_beq_eq_true h]
    rfl
  have p1 : (pairCount (dOrderTables 2) (dOrderTables 3) (fun x y => ordW 315 [x, y] 7) == 336) =
      true := by
    rw [hd2.1, hd3.1, pairCount_map (rk := r7K) fun x hx y hy =>
      ordW_unpack (ws := [x, y]) (by norm_num) (canon2 (hd2.2 _ hx) (hd3.2 _ hy)),
      Nat.eq_of_beq_eq_true pc1K]
    rfl
  have p2 : (pairCount (dOrderTables 2) (dOrderTables 3) (pairTest 315 7 4 2 3) == 336) = true := by
    rw [hd2.1, hd3.1, pairCount_map (rk := r74K) fun x hx y hy => pairT_of (hd2.2 _ hx) (hd3.2 _ hy),
      Nat.eq_of_beq_eq_true pc2K]
    rfl
  have cc : (countProducts 315 (commAll 315 [tblX, tblY]) (chainTables 315 fixCStrong fixCBase)
      (idT 315) == 1) = true := by
    rw [hX, hY, countProducts_sound fC_binds fC_perm FC.hl
      (f := commAll 315 [φ (FD.S 0), φ (FD.S 1)]) (fk := cmK) fun E cE => by
      unfold commAll cmK
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      rw [commT_unpack cE c0, commT_unpack cE c1]
      rfl, Nat.eq_of_beq_eq_true cntCK]
    rfl
  unfold tableCheck
  rw [o2, o3, pt, l2, a2, p1, p2, cc]
  rfl

end CertificateChecks.KernelJ2Cover

end
