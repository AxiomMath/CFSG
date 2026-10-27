
module

public import Certificates.Kernel.J2Cover.K20C
public import CFSG.Certificates.Kernel.J2CoverSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText TxtExternal
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.External
open CFSG.Monster.B.Co2 (allLt_iff)

theorem ordT_ofE {m X : Nat} (hm : 0 < m) (c : CnN 315 9 X) :
    ordTest 315 m (φ X) = ordPK 315 9 m (prodK 315 9 [X]) := by
  unfold ordTest
  exact CFSG.KC.J2Cover.ordW_unpack (ws := [X]) hm fun Y hY => by rw [List.mem_singleton.1 hY]; exact c

theorem hd2E : dOrderTables 2 = L2.map φ ∧ ∀ X ∈ L2, CnN 315 9 X := by
  unfold dOrderTables
  exact prodList_sound fD_binds fD_perm FD.hl fun X c => ordT_ofE (by norm_num) c

theorem hd3E : dOrderTables 3 = L3.map φ ∧ ∀ X ∈ L3, CnN 315 9 X := by
  unfold dOrderTables
  exact prodList_sound fD_binds fD_perm FD.hl fun X c => ordT_ofE (by norm_num) c

theorem pairT_ofE {X Y : Nat} (cX : CnN 315 9 X) (cY : CnN 315 9 Y) :
    pairTest 315 7 4 2 3 (φ X) (φ Y) = r74K X Y := by
  have hc : ∀ Z ∈ [X, Y, X, Y, Y], CnN 315 9 Z := by
    intro Z hZ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ
    rcases hZ with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h1 := CFSG.KC.J2Cover.ordW_unpack (n := 315) (w := 9) (m := 7) (ws := [X, Y]) (by norm_num)
    (canon2 cX cY)
  have h2 := CFSG.KC.J2Cover.ordW_unpack (n := 315) (w := 9) (m := 4) (ws := [X, Y, X, Y, Y]) (by norm_num) hc
  unfold pairTest r74K
  rw [← h1, ← h2]
  rfl

theorem tableCE : tableCheck = true := by
  have c0 : CnN 315 9 (FD.S 0) := by quickRfl
  have c1 : CnN 315 9 (FD.S 1) := by quickRfl
  have hX : tblX = φ (FD.S 0) := by unfold tblX; rw [fD_S 0 (by omega)]
  have hY : tblY = φ (FD.S 1) := by unfold tblY; rw [fD_S 1 (by omega)]
  have o2 : ordTest 315 2 tblX = true := by rw [hX, ordT_ofE (by norm_num) c0]; quickRfl
  have o3 : ordTest 315 3 tblY = true := by rw [hY, ordT_ofE (by norm_num) c1]; quickRfl
  have pt : pairTest 315 7 4 2 3 tblX tblY = true := by rw [hX, hY, pairT_ofE c0 c1]; quickRfl
  have l2 : ((dOrderTables 2).length == 21) = true := by
    rw [hd2E.1, List.length_map, ← lenL_eq, Nat.eq_of_beq_eq_true len2K]
    rfl
  have a2 : (dOrderTables 2).all (fun T => tblFix T == 11) = true := by
    rw [hd2E.1, List.all_map, List.all_eq_true]
    intro X hX
    have h := allL_spec fix2K X hX
    simp only [Function.comp_apply]
    rw [CFSG.KC.J2Cover.tblFix_unpack (hd2E.2 X hX), Nat.eq_of_beq_eq_true h]
    rfl
  have p1 : (pairCount (dOrderTables 2) (dOrderTables 3) (fun x y => ordW 315 [x, y] 7) == 336) =
      true := by
    rw [hd2E.1, hd3E.1, CFSG.KC.J2Cover.pairCount_map (rk := r7K) fun x hx y hy =>
      CFSG.KC.J2Cover.ordW_unpack (ws := [x, y]) (by norm_num) (canon2 (hd2E.2 _ hx) (hd3E.2 _ hy)),
      Nat.eq_of_beq_eq_true pc1K]
    rfl
  have p2 : (pairCount (dOrderTables 2) (dOrderTables 3) (pairTest 315 7 4 2 3) == 336) = true := by
    rw [hd2E.1, hd3E.1, CFSG.KC.J2Cover.pairCount_map (rk := r74K) fun x hx y hy =>
      pairT_ofE (hd2E.2 _ hx) (hd3E.2 _ hy), Nat.eq_of_beq_eq_true pc2K]
    rfl
  have cc : (countProducts 315 (commAll 315 [tblX, tblY]) (chainTables 315 fixCStrong fixCBase)
      (idT 315) == 1) = true := by
    rw [hX, hY, countProducts_sound fC_binds fC_perm FC.hl
      (f := commAll 315 [φ (FD.S 0), φ (FD.S 1)]) (fk := cmK) fun E cE => by
      unfold commAll cmK
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      rw [CFSG.KC.J2Cover.commT_unpack cE c0, CFSG.KC.J2Cover.commT_unpack cE c1]
      rfl, Nat.eq_of_beq_eq_true cntCK]
    rfl
  unfold tableCheck
  rw [o2, o3, pt, l2, a2, p1, p2, cc]
  rfl

theorem elemCE : elemCheck = true := by
  have w0 := fW_S 0 (by omega)
  have w1 := fW_S 1 (by omega)
  have c0 : CnN 315 9 (FW.S 0) := by quickRfl
  have c1 : CnN 315 9 (FW.S 1) := by quickRfl
  have ci0 : CnN 315 9 (FW.SI 0) := by quickRfl
  obtain ⟨e0, i0⟩ := invEqK_sound (allN_spec fW_perm 0 (by omega))
  have o4 : ordTest 315 4 (arrTable 315 fixWStrong[0]!) = true := by
    rw [w0, ordT_ofE (by norm_num) c0]
    quickRfl
  have o2 : ordTest 315 2 (arrTable 315 fixWStrong[1]!) = true := by
    rw [w1, ordT_ofE (by norm_num) c1]
    quickRfl
  have h3 : isInvA 315 fixWStrong[0]! (invCand 315 fixWStrong[0]!) = true := by
    rw [w0, e0]
    exact i0
  have h4 : eqA 315 (compA 315 fixWStrong[1]! (compA 315 fixWStrong[0]! fixWStrong[1]!))
      (invCand 315 fixWStrong[0]!) = true := by
    rw [w0, w1, e0, compA_unpackN c0 c1, compA_unpackN c1 (canon_pcN c0 c1),
      eqA_unpackN (canon_pcN c1 (canon_pcN c0 c1)) ci0]
    quickRfl
  have h5 : (!(eqA 315 fixWStrong[1]! (compA 315 fixWStrong[0]! fixWStrong[0]!))) = true := by
    rw [w0, w1, compA_unpackN c0 c0, eqA_unpackN c1 (canon_pcN c0 c0)]
    quickRfl
  have cU : CnN 315 9 FU := by quickRfl
  have h6 : invoList 315 fusionArr = true := by
    rw [hFU]
    quickRfl
  have h7 : movesList 315 fusionArr = true := by
    rw [hFU]
    quickRfl
  have h8 : (fixedCount 315 fusionArr == 15) = true := by
    rw [hFU]
    quickRfl
  have h9 : inC fusionArr = true := inC_of hFU (by quickRfl) (by quickRfl) (by quickRfl)
  have h10 : (!(inD fusionArr)) = true := by
    unfold inD
    rw [hFU, CFSG.KC.J2Cover.siftK_eq fD_binds fD_perm FD.hl cU]
    quickRfl
  have h11 : allLt 4 (fun k => isInvA 315 commArrs[k]! (invCand 315 commArrs[k]!) &&
      inD commArrs[k]!) = true := by
    refine allLt_iff.2 fun k hk => ?_
    obtain ⟨e, i⟩ := invEqK_sound (allN_spec kCAi k hk)
    rw [Bool.and_eq_true, hCA k hk, e]
    exact ⟨i, inD_of rfl (allN_spec kCAz k hk) (range_of_permOK (allN_spec kCAi k hk))
      (allN_spec kCAs k hk)⟩
  have fact : ∀ k < 4, invEqK 315 9 (mask 9) (315 * 9) (CA k) (pinvS 315 9 (mask 9) (CA k)) = true ∧
      CnN 315 9 (CA k) ∧ CnN 315 9 (pinvS 315 9 (mask 9) (CA k)) := fun k hk =>
    ⟨allN_spec kCAi k hk, allN_spec kCAc k hk, allN_spec kCAci k hk⟩
  obtain ⟨i0', a0, b0⟩ := fact 0 (by omega)
  obtain ⟨i1', a1, b1⟩ := fact 1 (by omega)
  obtain ⟨i2', a2, b2⟩ := fact 2 (by omega)
  obtain ⟨i3', a3, b3⟩ := fact 3 (by omega)
  have d0 : CnN 315 9 (FD.S 0) := by quickRfl
  have d1 : CnN 315 9 (FD.S 1) := by quickRfl
  have cc0 : CnN 315 9 (commP (CA 0) (CA 1)) := by quickRfl
  have cc1 : CnN 315 9 (commP (CA 2) (CA 3)) := by quickRfl
  have h12 : eqA 315 fixDStrong[0]! (commArr commArrs[0]! commArrs[1]!) = true := by
    rw [fD_S 0 (by omega), commArr_of (hCA 0 (by omega)) (hCA 1 (by omega)) i0' i1' a0 a1 b0 b1,
      eqA_unpackN d0 cc0]
    quickRfl
  have h13 : eqA 315 fixDStrong[1]! (commArr commArrs[2]! commArrs[3]!) = true := by
    rw [fD_S 1 (by omega), commArr_of (hCA 2 (by omega)) (hCA 3 (by omega)) i2' i3' a2 a3 b2 b3,
      eqA_unpackN d1 cc1]
    quickRfl
  unfold elemCheck
  rw [o4, o2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  rfl

end CertificateChecks.KernelJ2Cover

end
