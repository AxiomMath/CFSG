
module

public import Certificates.Kernel.J2Cover.K20B
public import CFSG.Monster.B.Co2.PermArr
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
open CFSG.Monster.B.Co2 (allLt_iff)

@[expose] noncomputable def CA (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (packL 9 (natsK C.commArrs.c0)).1
    (fun j _ => Nat.rec (motive := fun _ => Nat) (packL 9 (natsK C.commArrs.c1)).1
      (fun j' _ => Nat.rec (motive := fun _ => Nat) (packL 9 (natsK C.commArrs.c2)).1
        (fun _ _ => (packL 9 (natsK C.commArrs.c3)).1) j') j) k

theorem hCA (k : Nat) (hk : k < 4) : commArrs[k]! = unpack 315 9 (CA k) := by
  interval_cases k
  · exact bind_txt rfl C.commArrs.e0 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.commArrs.e1 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.commArrs.e2 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.commArrs.e3 (by quickRfl) (by quickRfl)

theorem hFU : fusionArr = unpack 315 9 FU :=
  bind_txt rfl C.fusionArr.e0 (by quickRfl) (by quickRfl)

theorem kCAi : allN 4 (fun k => invEqK 315 9 (mask 9) (315 * 9) (CA k)
    (pinvS 315 9 (mask 9) (CA k))) = true := by
  quickRfl

theorem kCAc : allN 4 (fun k => canonK 315 9 (mask 9) (315 * 9) (CA k)) = true := by quickRfl

theorem kCAci : allN 4 (fun k => canonK 315 9 (mask 9) (315 * 9) (pinvS 315 9 (mask 9) (CA k))) =
    true := by
  quickRfl

theorem kCAz : allN 4 (fun k => Nat.beq (Nat.shiftRight (CA k) (315 * 9)) 0) = true := by quickRfl

theorem kCAs : allN 4 (fun k =>
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) FD.LR FD.TRI FD.BP 1 0 (CA k)) = true := by
  quickRfl

@[expose] noncomputable def commP (A B : Nat) : Nat :=
  pcomp 315 9 (mask 9) A (pcomp 315 9 (mask 9) B (pcomp 315 9 (mask 9) (pinvS 315 9 (mask 9) A)
    (pinvS 315 9 (mask 9) B)))

theorem commArr_of {a b : Array Nat} {A B : Nat} (ha : a = unpack 315 9 A) (hb : b = unpack 315 9 B)
    (iA : invEqK 315 9 (mask 9) (315 * 9) A (pinvS 315 9 (mask 9) A) = true)
    (iB : invEqK 315 9 (mask 9) (315 * 9) B (pinvS 315 9 (mask 9) B) = true)
    (cA : CnN 315 9 A) (cB : CnN 315 9 B) (cAi : CnN 315 9 (pinvS 315 9 (mask 9) A))
    (cBi : CnN 315 9 (pinvS 315 9 (mask 9) B)) :
    commArr a b = unpack 315 9 (commP A B) := by
  unfold commArr commP
  rw [ha, hb, (invEqK_sound iA).1, (invEqK_sound iB).1, compA_unpackN cAi cBi,
    compA_unpackN cB (canon_pcN cAi cBi), compA_unpackN cA (canon_pcN cB (canon_pcN cAi cBi))]

theorem elemC : elemCheck = true := by
  have w0 := fW_S 0 (by omega)
  have w1 := fW_S 1 (by omega)
  have c0 : CnN 315 9 (FW.S 0) := by quickRfl
  have c1 : CnN 315 9 (FW.S 1) := by quickRfl
  have ci0 : CnN 315 9 (FW.SI 0) := by quickRfl
  obtain ⟨e0, i0⟩ := invEqK_sound (allN_spec fW_perm 0 (by omega))
  have o4 : ordTest 315 4 (arrTable 315 fixWStrong[0]!) = true := by
    rw [w0, ordT_of (by norm_num) c0]
    quickRfl
  have o2 : ordTest 315 2 (arrTable 315 fixWStrong[1]!) = true := by
    rw [w1, ordT_of (by norm_num) c1]
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
    rw [hFU, siftK_eq fD_binds fD_perm FD.hl cU]
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
