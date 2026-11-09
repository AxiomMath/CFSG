module

public import Certificates.Kernel.H13.O3Tac
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem o3_ovB0 : CFSG.Quasithin.H13.O3Cert.ovB 0 = true := by o3_tac

@[expose] def o3ovF (c : ℕ) (y : List ℕ) : Bool :=
  mv8 y (vS c) == vS c ||
    (Std.HashSet.ofList ((List.range 256).filter fun u =>
      (pE c).any fun p₁ => mv8 p₁ u != u && (pE c).any fun p₂ =>
        mv8 p₂ u != u && mv8 p₂ u != mv8 p₁ u)).contains (mv8 y (vS c)) ||
    (Std.HashSet.ofList (mE c)).contains y ||
    (let B := elemsOf (pG c ++ [y]) (3 * pOrd c + 1)
     decide (3 * pOrd c < B.length) && nodupB B)

set_option maxHeartbeats 0 in
theorem o3_ovB_eq (c : ℕ) : CFSG.Quasithin.H13.O3Cert.ovB c =
    ((Std.HashSet.ofList (gamE c)).contains (mRep c) && subB (pG c ++ [mRep c]) (mE c) &&
      (mE c).length == 3 * pOrd c && (gamE c).all (o3ovF c) &&
      subB (CFSG.Quasithin.H13.S7Cert.oddOf (mE c)) (oME c) &&
      ((oME c).all fun y => [0, (wS c).1, (wS c).2].contains (mv8 y (vS c) ^^^ vS c)) &&
      ((oME c).any fun y => mv8 y (vS c) ^^^ vS c == (wS c).1) &&
      ((oME c).any fun y => mv8 y (vS c) ^^^ vS c == (wS c).2) && (wS c).1 ^^^ (wS c).2 == vS c) := by
  delta CFSG.Quasithin.H13.O3Cert.ovB o3ovF
  rfl

set_option maxHeartbeats 0 in
theorem o3_ovC0 : ((D.omNL.drop (0 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC1 : ((D.omNL.drop (1 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC2 : ((D.omNL.drop (2 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC3 : ((D.omNL.drop (3 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC4 : ((D.omNL.drop (4 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC5 : ((D.omNL.drop (5 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC6 : ((D.omNL.drop (6 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC7 : ((D.omNL.drop (7 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC8 : ((D.omNL.drop (8 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC9 : ((D.omNL.drop (9 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC10 : ((D.omNL.drop (10 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovC11 : ((D.omNL.drop (11 * 1200)).take 1200).all (o3ovF 1 ∘ unpackM) = true := by
  simp only [Function.comp_def, o3ovF]
  o3_tac

theorem o3_ovY1 : (gamE 1).all (o3ovF 1) = true := by
  rw [show gamE 1 = omNE from rfl, omNE_eq, List.all_map]
  apply CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 1200 12 (by decide +kernel)
  intro j hj
  interval_cases j
  · exact o3_ovC0
  · exact o3_ovC1
  · exact o3_ovC2
  · exact o3_ovC3
  · exact o3_ovC4
  · exact o3_ovC5
  · exact o3_ovC6
  · exact o3_ovC7
  · exact o3_ovC8
  · exact o3_ovC9
  · exact o3_ovC10
  · exact o3_ovC11

set_option maxHeartbeats 0 in
theorem o3_ovB1 : CFSG.Quasithin.H13.O3Cert.ovB 1 = true := by
  rw [o3_ovB_eq, o3_ovY1, Bool.and_true]
  o3_tac

set_option maxHeartbeats 0 in
theorem o3_kB0 : kB 0 = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_kB1 : kB 1 = true := by o3_tac

end CertificateChecks.KernelH13

end
