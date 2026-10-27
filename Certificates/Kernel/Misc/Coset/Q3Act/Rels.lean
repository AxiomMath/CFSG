module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverInputs
public import CFSG.Certificates.Kernel.Orders.Fi24p.RelsBind
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.KAct.Q3

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

@[expose] def liftN (l : ℕ × Bool) : Fin nG × Bool := (⟨l.1 % nG, Nat.mod_lt _ (by norm_num)⟩, l.2)

@[expose] def wsQN (X : List (List (ℕ × Bool))) : List (List (Fin nG × Bool)) :=
  (X.filter fun w => !(w.any fun l => l.1 == 8)).map (·.map liftN) ++
    [(X.getD sqIdx []).map liftN] ++
    (List.range 11).flatMap fun k =>
      [(X.getD (repIdx3.getD k 0) []).map liftN ++ [(zeta k, false)],
        List.replicate 9 (zeta k, true)] ++
      (List.range 11).map fun i =>
        [(zeta k, true), (Fin.ofNat nG i, true), (zeta k, false), (Fin.ofNat nG i, false)]

@[expose] def toNw {m : ℕ} (w : List (Fin m × Bool)) : List (ℕ × Bool) :=
  w.map fun l => (l.1.val, l.2)

theorem x0_letters : X0.map toNw = CFSG.KD.OrdFi24p.rels := by
  have h := CFSG.KD.OrdFi24p.rels_eq
  rw [TauCeti.GroupPresentation.relatorLetters_def] at h
  exact h

theorem map_liftL (w : List (Fin m0 × Bool)) : w.map liftL = (toNw w).map liftN := by
  rw [toNw, List.map_map]
  rfl

theorem wsQN_map : wsQN (X0.map toNw) = wsQ := by
  have hd : ∀ i, (X0.map toNw).getD i [] = toNw (X0.getD i []) := by
    intro i
    rw [show ([] : List (ℕ × Bool)) = toNw [] from rfl, List.getD_map]
  have hf : (X0.map toNw).filter (fun w => !(w.any fun l => l.1 == 8)) =
      (X0.filter fun w => !(w.any fun l => l.1.val == 8)).map toNw := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro w _
    simp only [Function.comp_apply, toNw, List.any_map]
    rfl
  unfold wsQN wsQ centralWords3
  rw [hf, hd, List.map_map]
  simp only [hd, Function.comp_def, ← map_liftL]

theorem wsQ_eq : wsQ = wsQN CFSG.KD.OrdFi24p.rels := by
  rw [← x0_letters, wsQN_map]

theorem sq_letters : (X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) = [(8, true), (8, true)] := by
  have h : (X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) = CFSG.KD.OrdFi24p.rels.getD sqIdx [] := by
    rw [← x0_letters, show ([] : List (ℕ × Bool)) = toNw [] from rfl, List.getD_map]
    rfl
  rw [h]
  decide +kernel

end CFSG.KAct.Q3
