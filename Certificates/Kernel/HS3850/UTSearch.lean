module

public import Certificates.Kernel.HS3850.UTDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Data.Kernel.PkPow

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.KC.InvTabK

theorem all_take_drop {α : Type} (L : List α) (F : α → Bool) (b : Nat) :
    L.all F = ((L.take b).all F && (L.drop b).all F) := by
  rw [← List.all_append, List.take_append_drop]

theorem rank6_q0a : (((greedyExtF 191 cK pK []).take 48).take 6).all
    (fun x => forallGreedyF 191 cK pK (fun _ => false) 5 [x]) = true := by
  quickRfl

theorem rank6_q0b : ((((greedyExtF 191 cK pK []).take 48).drop 6).take 8).all
    (fun x => forallGreedyF 191 cK pK (fun _ => false) 5 [x]) = true := by
  quickRfl

theorem rank6_q0c : (((((greedyExtF 191 cK pK []).take 48).drop 6).drop 8).take 12).all
    (fun x => forallGreedyF 191 cK pK (fun _ => false) 5 [x]) = true := by
  quickRfl

theorem rank6_q0d : (((((greedyExtF 191 cK pK []).take 48).drop 6).drop 8).drop 12).all
    (fun x => forallGreedyF 191 cK pK (fun _ => false) 5 [x]) = true := by
  quickRfl

theorem rank6_q0 : ((greedyExtF 191 cK pK []).take 48).all
    (fun x => forallGreedyF 191 cK pK (fun _ => false) 5 [x]) = true := by
  rw [all_take_drop _ _ 6, all_take_drop (((greedyExtF 191 cK pK []).take 48).drop 6) _ 8,
    all_take_drop ((((greedyExtF 191 cK pK []).take 48).drop 6).drop 8) _ 12,
    rank6_q0a, rank6_q0b, rank6_q0c, rank6_q0d]
  rfl

theorem rank6_q1 : (((greedyExtF 191 cK pK []).drop 48).take 48).all
    (fun x => forallGreedyF 191 cK pK (fun _ => false) 5 [x]) = true := by
  quickRfl

theorem rank6_q2 : ((((greedyExtF 191 cK pK []).drop 48).drop 48).take 48).all
    (fun x => forallGreedyF 191 cK pK (fun _ => false) 5 [x]) = true := by
  quickRfl

theorem rank6_q3 : ((((greedyExtF 191 cK pK []).drop 48).drop 48).drop 48).all
    (fun x => forallGreedyF 191 cK pK (fun _ => false) 5 [x]) = true := by
  quickRfl

theorem rank6 : forallGreedyF 191 cK pK (fun _ => false) 6 [] = true := by
  rw [forallGreedyF, all_take_drop _ _ 48, all_take_drop ((greedyExtF 191 cK pK []).drop 48) _ 48,
    all_take_drop (((greedyExtF 191 cK pK []).drop 48).drop 48) _ 48,
    rank6_q0, rank6_q1, rank6_q2, rank6_q3]
  rfl

theorem rank4_q0 : ((greedyExtF 191 cK pK []).take 48).all
    (fun x => forallGreedyF 191 cK pK pred4K 3 [x]) = true := by
  quickRfl

theorem rank4_q1 : (((greedyExtF 191 cK pK []).drop 48).take 48).all
    (fun x => forallGreedyF 191 cK pK pred4K 3 [x]) = true := by
  quickRfl

theorem rank4_q2 : ((((greedyExtF 191 cK pK []).drop 48).drop 48).take 48).all
    (fun x => forallGreedyF 191 cK pK pred4K 3 [x]) = true := by
  quickRfl

theorem rank4_q3 : ((((greedyExtF 191 cK pK []).drop 48).drop 48).drop 48).all
    (fun x => forallGreedyF 191 cK pK pred4K 3 [x]) = true := by
  quickRfl

theorem rank4 : forallGreedyF 191 cK pK pred4K 4 [] = true := by
  rw [forallGreedyF, all_take_drop _ _ 48, all_take_drop ((greedyExtF 191 cK pK []).drop 48) _ 48,
    all_take_drop (((greedyExtF 191 cK pK []).drop 48).drop 48) _ 48,
    rank4_q0, rank4_q1, rank4_q2, rank4_q3]
  rfl

theorem rank5_q0a : (((greedyExtF 191 cK pK []).take 48).take 6).all
    (fun x => forallGreedyF 191 cK pK pred5K 4 [x]) = true := by
  quickRfl

theorem rank5_q0b : ((((greedyExtF 191 cK pK []).take 48).drop 6).take 8).all
    (fun x => forallGreedyF 191 cK pK pred5K 4 [x]) = true := by
  quickRfl

theorem rank5_q0c : (((((greedyExtF 191 cK pK []).take 48).drop 6).drop 8).take 12).all
    (fun x => forallGreedyF 191 cK pK pred5K 4 [x]) = true := by
  quickRfl

theorem rank5_q0d : (((((greedyExtF 191 cK pK []).take 48).drop 6).drop 8).drop 12).all
    (fun x => forallGreedyF 191 cK pK pred5K 4 [x]) = true := by
  quickRfl

theorem rank5_q0 : ((greedyExtF 191 cK pK []).take 48).all
    (fun x => forallGreedyF 191 cK pK pred5K 4 [x]) = true := by
  rw [all_take_drop _ _ 6, all_take_drop (((greedyExtF 191 cK pK []).take 48).drop 6) _ 8,
    all_take_drop ((((greedyExtF 191 cK pK []).take 48).drop 6).drop 8) _ 12,
    rank5_q0a, rank5_q0b, rank5_q0c, rank5_q0d]
  rfl

theorem rank5_q1 : (((greedyExtF 191 cK pK []).drop 48).take 48).all
    (fun x => forallGreedyF 191 cK pK pred5K 4 [x]) = true := by
  quickRfl

theorem rank5_q2 : ((((greedyExtF 191 cK pK []).drop 48).drop 48).take 48).all
    (fun x => forallGreedyF 191 cK pK pred5K 4 [x]) = true := by
  quickRfl

theorem rank5_q3 : ((((greedyExtF 191 cK pK []).drop 48).drop 48).drop 48).all
    (fun x => forallGreedyF 191 cK pK pred5K 4 [x]) = true := by
  quickRfl

theorem rank5 : forallGreedyF 191 cK pK pred5K 5 [] = true := by
  rw [forallGreedyF, all_take_drop _ _ 48, all_take_drop ((greedyExtF 191 cK pK []).drop 48) _ 48,
    all_take_drop (((greedyExtF 191 cK pK []).drop 48).drop 48) _ 48,
    rank5_q0, rank5_q1, rank5_q2, rank5_q3]
  rfl

end CertificateChecks.KernelHS3850.UT

end
