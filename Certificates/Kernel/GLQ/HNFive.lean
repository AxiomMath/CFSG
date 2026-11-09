module

public import Certificates.Kernel.GLQ.HNTwo
public import CFSG.RankThree.PartOne.KS.HNFiveInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_json CertificateChecks.KernelGLQ.HNFiveK.D "Certificates/Kernel/GLQ/data/hn5.json"
  7817639 10378596024030947821
  (A : Nat) (B : Nat) (B2 : Nat) (S36 : List (Nat × Nat × Nat)) (S71 : List (Nat × Nat × Nat))
  (S101 : List (Nat × Nat × Nat)) (S136 : List (Nat × Nat × Nat)) (S171 : List (Nat × Nat × Nat))
  (S201 : List (Nat × Nat × Nat)) (S241 : List (Nat × Nat × Nat)) (S280 : List (Nat × Nat × Nat))

namespace CertificateChecks.KernelGLQ.HNFiveK

open CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.RankThree.PartOne.KS.HNFive
open CertificateChecks.KernelGLQ.HNTwo

@[expose] noncomputable def checkHN5 (prog : List Instr) (A B : Nat) : Bool :=
  vld A && vld B && forceB (powN O5 3 B 2) fun B2 =>
    runK O5 prog (initRegsN O5 hnFiveN (A, A) (B, B2)) fun R => relsOK O5 R

@[expose] noncomputable def snap (L : List (Nat × Nat × Nat)) : Array (Nat × Nat) :=
  L.foldl (fun R e => R.setIfInBounds e.1 e.2) (initRegsN O5 hnFiveN (O5.one, O5.one) (O5.one, O5.one))

@[expose] def regsEq : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], [] => true
  | a :: l, b :: m => Nat.beq a.1 b.1 && Nat.beq a.2 b.2 && regsEq l m
  | _, _ => false

theorem regsEq_sound : ∀ {l m : List (Nat × Nat)}, regsEq l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    simp only [regsEq, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [Prod.ext (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2), regsEq_sound h3]
  | [], _ :: _, h => by simp [regsEq] at h
  | _ :: _, [], h => by simp [regsEq] at h

@[expose] noncomputable def segOK (a b : Nat) (S T : Array (Nat × Nat)) : Bool :=
  runK O5 ((hnFiveProg.drop a).take (b - a)) S fun R => regsEq R.toList T.toList

theorem seg_eq {a b : Nat} {S T : Array (Nat × Nat)} (h : segOK a b S T = true) :
    runProgN O5 S ((hnFiveProg.drop a).take (b - a)) = T := by
  unfold segOK at h
  rw [runK_eq] at h
  exact Array.toList_inj.mp (regsEq_sound h)

theorem run_split (a b : Nat) (hab : a ≤ b) (S : Array (Nat × Nat)) :
    runProgN O5 S (hnFiveProg.drop a) =
      runProgN O5 (runProgN O5 S ((hnFiveProg.drop a).take (b - a))) (hnFiveProg.drop b) := by
  conv_lhs => rw [← List.take_append_drop (b - a) (hnFiveProg.drop a)]
  rw [runProgN, List.foldl_append, List.drop_drop, Nat.add_sub_cancel' hab]
  rfl

theorem kA : Nat.beq (pay HS1.chars) D.A = true := by quickRfl

theorem kB : Nat.beq (pay HS2.chars) D.B = true := by quickRfl

theorem kB2 : Nat.beq (powN O5 3 D.B 2) D.B2 = true := by quickRfl

theorem kvA : vld D.A = true := by quickRfl

theorem kvB : vld D.B = true := by quickRfl

theorem k0 : segOK 0 36 (initRegsN O5 hnFiveN (D.A, D.A) (D.B, D.B2)) (snap D.S36) = true := by
  quickRfl

theorem k1 : segOK 36 71 (snap D.S36) (snap D.S71) = true := by quickRfl

theorem k2 : segOK 71 101 (snap D.S71) (snap D.S101) = true := by quickRfl

theorem k3 : segOK 101 136 (snap D.S101) (snap D.S136) = true := by quickRfl

theorem k4 : segOK 136 171 (snap D.S136) (snap D.S171) = true := by quickRfl

theorem k5 : segOK 171 201 (snap D.S171) (snap D.S201) = true := by quickRfl

theorem k6 : segOK 201 241 (snap D.S201) (snap D.S241) = true := by quickRfl

theorem k7 : segOK 241 280 (snap D.S241) (snap D.S280) = true := by quickRfl

theorem kRels : relsOK O5 (snap D.S280) = true := by quickRfl

theorem hrun : runProgN O5 (initRegsN O5 hnFiveN (D.A, D.A) (D.B, D.B2)) hnFiveProg =
    snap D.S280 := by
  have e : hnFiveProg.drop 280 = [] := rfl
  rw [← List.drop_zero (l := hnFiveProg), run_split 0 36 (by norm_num), seg_eq k0,
    run_split 36 71 (by norm_num), seg_eq k1, run_split 71 101 (by norm_num), seg_eq k2,
    run_split 101 136 (by norm_num), seg_eq k3, run_split 136 171 (by norm_num), seg_eq k4,
    run_split 171 201 (by norm_num), seg_eq k5, run_split 201 241 (by norm_num), seg_eq k6,
    run_split 241 280 (by norm_num), seg_eq k7, e]
  rfl

theorem kHN5 : forceB (pay HS1.chars) (fun A => forceB (pay HS2.chars) fun B =>
    checkHN5 hnFiveProg A B) = true := by
  rw [forceB_eq, forceB_eq, Nat.eq_of_beq_eq_true kA, Nat.eq_of_beq_eq_true kB]
  unfold checkHN5
  rw [forceB_eq, Nat.eq_of_beq_eq_true kB2, runK_eq, hrun, kvA, kvB, kRels]
  rfl

end CertificateChecks.KernelGLQ.HNFiveK

end
