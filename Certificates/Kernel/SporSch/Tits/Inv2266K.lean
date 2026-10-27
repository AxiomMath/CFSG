module

public import Certificates.Kernel.SporSch.Tits.Inv2266M
public import Certificates.Kernel.SporSch.Tits.Central2263
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel

theorem tW : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 titsTWord (wK titsTWord) =
    true := by
  unfold wordEqK
  quickRfl
theorem tB : Nat.beq (wK titsTWord) TitsT = true := by quickRfl
theorem cT : C TitsT := by quickRfl
theorem cG1 : C (TitsText.F 1) := by quickRfl
theorem cG1i : C (pinv (TitsText.F 1)) := by quickRfl

theorem kTK : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0 TitsT =
    true := by quickRfl
theorem kTne : neIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsT = true := by quickRfl
theorem kTsq : sqIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsT = true := by quickRfl
theorem k5 : allN 3 (fun j => sS (pc (pc (TitsText.F 1) (TitsS.S j)) (pinv (TitsText.F 1)))) = true := by
  quickRfl
theorem k6 : sS (pc (TitsText.F 1) (TitsText.F 1)) = true := by quickRfl
theorem k7 : bIf(sS (TitsText.F 1), false, true) = true := by quickRfl

@[expose] noncomputable def lIC (bw : Bool × List Int) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun _ wd => lettersK 13 wd) bw

@[expose] noncomputable def gIC (bw : Bool × List Int) (y : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun b wd =>
    conjW TitsD.S TitsD.SI wd (Bool.rec (motive := fun _ => Nat) TitsT TitsZ b) y) bw

theorem zipA_append {α : Type} {g : α → Nat → Bool} :
    ∀ {A1 A2 : List α} {L1 L2 : List Nat}, zipA g A1 L1 = true → zipA g A2 L2 = true →
      zipA g (A1 ++ A2) (L1 ++ L2) = true
  | [], _, [], _, _, h => h
  | [], _, _ :: _, _, h, _ => (Bool.false_ne_true h).elim
  | _ :: _, _, [], _, h, _ => (Bool.false_ne_true h).elim
  | a :: A1, A2, l :: L1, L2, h, h2 => by
    have h' : Bool.rec (motive := fun _ => Bool) false (zipA g A1 L1) (g a l) = true := h
    obtain ⟨h1, h3⟩ := (bAnd_iff _ _).1 h'
    change Bool.rec (motive := fun _ => Bool) false (zipA g (A1 ++ A2) (L1 ++ L2)) (g a l) = true
    rw [h1, zipA_append h3 h2]

theorem zipA_chunks {α : Type} {g : α → Nat → Bool} (c : Nat) :
    ∀ (m : Nat) (A : List α) (L : List Nat), A.length ≤ c * m → L.length ≤ c * m →
      (∀ i < m, zipA g ((A.drop (c * i)).take c) ((L.drop (c * i)).take c) = true) →
      zipA g A L = true
  | 0, A, L, hA, hL, _ => by
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hA),
      List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hL)]
    rfl
  | m + 1, A, L, hA, hL, h => by
    rw [← List.take_append_drop c A, ← List.take_append_drop c L]
    refine zipA_append (by simpa using h 0 (by omega)) (zipA_chunks c m _ _ ?_ ?_ fun i hi => ?_)
    · rw [List.length_drop, Nat.mul_succ] at *
      omega
    · rw [List.length_drop, Nat.mul_succ] at *
      omega
    · simpa only [List.drop_drop, Nat.mul_succ, Nat.add_comm] using h (i + 1) (by omega)

theorem kIC : allA lIC titsInvCert = true := by quickRfl
theorem kICz0 : zipA gIC ((titsInvCert.drop (16 * 0)).take 16) ((TitsIC.drop (16 * 0)).take 16) =
    true := by quickRfl
theorem kICz1 : zipA gIC ((titsInvCert.drop (16 * 1)).take 16) ((TitsIC.drop (16 * 1)).take 16) =
    true := by quickRfl
theorem kICz2 : zipA gIC ((titsInvCert.drop (16 * 2)).take 16) ((TitsIC.drop (16 * 2)).take 16) =
    true := by quickRfl
theorem kICz3 : zipA gIC ((titsInvCert.drop (16 * 3)).take 16) ((TitsIC.drop (16 * 3)).take 16) =
    true := by quickRfl
theorem kICz4 : zipA gIC ((titsInvCert.drop (16 * 4)).take 16) ((TitsIC.drop (16 * 4)).take 16) =
    true := by quickRfl
theorem kICz5 : zipA gIC ((titsInvCert.drop (16 * 5)).take 16) ((TitsIC.drop (16 * 5)).take 16) =
    true := by quickRfl
theorem kICz6 : zipA gIC ((titsInvCert.drop (16 * 6)).take 16) ((TitsIC.drop (16 * 6)).take 16) =
    true := by quickRfl
theorem kICz7 : zipA gIC ((titsInvCert.drop (16 * 7)).take 16) ((TitsIC.drop (16 * 7)).take 16) =
    true := by quickRfl
theorem kICz8 : zipA gIC ((titsInvCert.drop (16 * 8)).take 16) ((TitsIC.drop (16 * 8)).take 16) =
    true := by quickRfl
theorem kICl : Nat.ble titsInvCert.length (16 * 9) = true := by quickRfl
theorem kICll : Nat.ble TitsIC.length (16 * 9) = true := by quickRfl

theorem kICz : zipA gIC titsInvCert TitsIC = true :=
  zipA_chunks 16 9 _ _ (Nat.le_of_ble_eq_true kICl) (Nat.le_of_ble_eq_true kICll) fun i hi => by
    match i, hi with
    | 0, _ => exact kICz0
    | 1, _ => exact kICz1
    | 2, _ => exact kICz2
    | 3, _ => exact kICz3
    | 4, _ => exact kICz4
    | 5, _ => exact kICz5
    | 6, _ => exact kICz6
    | 7, _ => exact kICz7
    | 8, _ => exact kICz8

theorem kICc : allL (fun y => canonK 1755 11 (mask 11) (1755 * 11) y) TitsIC = true := by quickRfl

@[expose] def fixPts : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 18, 19, 21, 25, 26, 31, 32, 37, 46, 57, 68]

theorem kFix : allN 1755 (fun p => bIf(Nat.beq (pg 11 (mask 11) TitsT p) p, memN p fixPts, true)) =
    true := by quickRfl

@[expose] noncomputable def okFW (pw : Nat × List Int) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun p wd => bAnd(lettersK 13 wd,
    Nat.beq (wPt TitsD.S TitsD.SI wd 0) p)) pw

theorem kFW : allA okFW titsFixWords = true := by quickRfl

@[expose] noncomputable def qEx (pw : Nat × List Int) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun p _ => Nat.blt 2 p) pw

@[expose] noncomputable def gEx (pw : Nat × List Int) (y : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun _ wd => exclW TitsD.S TitsD.SI wd TitsT y) pw

@[expose] noncomputable def zipAF {α : Type} (q : α → Bool) (g : α → Nat → Bool) (A : List α) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun a _ ih L => bIf(q a,
      List.rec (motive := fun _ => Bool) false (fun l L' _ => bAnd(g a l, ih L')) L, ih L)) A

theorem kEXz : zipAF qEx gEx titsFixWords TitsEX = true := by quickRfl
theorem kEXc : allL (fun y => canonK 1755 11 (mask 11) (1755 * 11) y) TitsEX = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsInv

end
