module

public import Certificates.Kernel.LocalComp.Co3SurjData
public import Certificates.Kernel.LocalComp.Co3SurjTData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Surj

open CFSG.KC.SurjK CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.Loop
open CFSG.KS (lget)
open CFSG.EvenSmallLie.SympSix.Co3Ident

@[expose] noncomputable def matWFrom (d : Nat) (F : Int → Nat) (w : List Int) (T : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) T (fun z _ ih => strictN ih fun T => mulF d (F z) T) w

theorem matW_append (d : Nat) (F : Int → Nat) (u v : List Int) :
    matW d F (u ++ v) = matWFrom d F u (matW d F v) := by
  induction u with
  | nil => rfl
  | cons z u ih =>
    change strictN (matW d F (u ++ v)) (fun T => mulF d (F z) T) =
      strictN (matWFrom d F u (matW d F v)) (fun T => mulF d (F z) T)
    rw [ih]

noncomputable abbrev FB : Int → Nat := baseF CS.A CS.AI CS.B CS.BI

@[expose] noncomputable def WI (i : Nat) : List Int := IW.W.toArray[i]!

@[expose] noncomputable def stepB (k : Nat) : Bool :=
  Nat.beq (matWFrom 22 FB (WI (sDok.getD k 0)) (T3.getD (k + 1) 0)) (T3.getD k 0)

theorem kStep0 : [0, 1, 2, 3, 4, 5, 6].all stepB = true := by quickRfl
theorem kStep1 : [7, 8, 9, 10, 11, 12].all stepB = true := by quickRfl
theorem kStep2 : [13, 14, 15, 16, 17, 18, 19].all stepB = true := by quickRfl
theorem kStep3 : [20, 21, 22, 23, 24, 25].all stepB = true := by quickRfl
theorem kEnd : Nat.beq (T3.getD 26 0) (idF 22) = true := by quickRfl

theorem step (k : Nat) (hk : k < 26) : stepB k = true := by
  interval_cases k
  all_goals first
    | (apply List.all_eq_true.1 kStep0; decide)
    | (apply List.all_eq_true.1 kStep1; decide)
    | (apply List.all_eq_true.1 kStep2; decide)
    | (apply List.all_eq_true.1 kStep3; decide)

theorem sDok_length : sDok.length = 26 := rfl

theorem suffix (n : Nat) : ∀ k, k + n = 26 →
    matW 22 FB ((sDok.drop k).flatMap WI) = T3.getD k 0 := by
  induction n with
  | zero =>
    intro k hk
    subst hk
    exact (Nat.eq_of_beq_eq_true kEnd).symm
  | succ n ih =>
    intro k hk
    have hk' : k < sDok.length := by rw [sDok_length]; omega
    rw [List.drop_eq_getElem_cons hk', List.flatMap_cons, matW_append,
      ih (k + 1) (by omega), ← List.getD_eq_getElem sDok 0 hk']
    exact Nat.eq_of_beq_eq_true (step k (by omega))

theorem kImg3 : matW 22 FB (sDok.flatMap WI) = lget CS.Ims 3 := by
  have h := suffix 26 0 rfl
  rw [List.drop_zero] at h
  rw [h]
  exact Nat.eq_of_beq_eq_true kT0
where
  kT0 : Nat.beq (T3.getD 0 0) (lget CS.Ims 3) = true := by quickRfl

end CertificateChecks.KernelLC.Co3Surj

end
