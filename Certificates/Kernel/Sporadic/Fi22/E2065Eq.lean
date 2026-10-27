module

public import Certificates.Kernel.Sporadic.Fi22.E2065B
public import Certificates.Kernel.Sporadic.Fi22.E2065

public section

namespace CertificateChecks.KernelSpor.Fi22CentB

open CFSG.KC.YModel CFSG.Sporadic.FischerOddCore

theorem decChunkC_append (len : Nat) : ∀ (N : Nat) (t u : List Char),
    decChunkC len N t ++ u = decChunkC len N (t ++ u) := by
  induction len with
  | zero => intro N t u; rfl
  | succ n ih => intro N t u; exact congrArg (List.cons _) (ih _ t u)

theorem charsOf_append : ∀ a b : List (Nat × Nat), charsOf (a ++ b) = charsOf a ++ charsOf b
  | [], _ => rfl
  | (N, len) :: a, b => by
    change decChunkC len N (charsOf (a ++ b)) = decChunkC len N (charsOf a) ++ charsOf b
    rw [charsOf_append a b, decChunkC_append]

theorem charsOf_join {W A A' V : List (Nat × Nat)} {w x y : Nat × Nat}
    (hW : (W == A' ++ w :: V) = true) (hA : (A == A' ++ [x]) = true)
    (hw : (charsOf [w] == charsOf [x, y]) = true) : charsOf W = charsOf A ++ charsOf (y :: V) := by
  rw [beq_iff_eq.mp hW, beq_iff_eq.mp hA, charsOf_append, charsOf_append]
  have e1 : charsOf (w :: V) = charsOf [w] ++ charsOf V := charsOf_append [w] V
  have e2 : charsOf (y :: V) = charsOf [y] ++ charsOf V := charsOf_append [y] V
  have e3 : charsOf [x, y] = charsOf [x] ++ charsOf [y] := charsOf_append [x] [y]
  rw [e1, e2, beq_iff_eq.mp hw, e3]
  simp only [List.append_assoc]

theorem chars_eq : charsOf W.CH = charsOf Q0.CH ++ (charsOf Q1.CH ++ (charsOf Q2.CH ++ charsOf Q3.CH)) := by
  rw [charsOf_join split0 last0 join1, charsOf_join split1 last1 join2,
    charsOf_join split2 last2 join3, beq_iff_eq.mp split3]

theorem text_eq : fi22Cent3510Text = Fi22E2065.textP := by
  rw [W.eq, Fi22E2065.textP, Q0.eq, Q1.eq, Q2.eq, Q3.eq, chars_eq]
  simp only [String.ofList_append, String.append_assoc]

end CertificateChecks.KernelSpor.Fi22CentB

end
