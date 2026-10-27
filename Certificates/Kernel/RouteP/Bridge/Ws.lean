module

public import Certificates.Kernel.RouteP.Bridge.Defs
public import CFSG.Certificates.Kernel.Orders.Fi24p.RelsBind
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelRouteP

open CFSG.KD.RouteP CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

@[expose] def toNw {n : ℕ} (w : List (Fin n × Bool)) : List (ℕ × Bool) := w.map fun l => (l.1.val, l.2)

theorem x0_letters : X0.map toNw = CFSG.KD.OrdFi24p.rels := by
  have h := CFSG.KD.OrdFi24p.rels_eq
  rw [TauCeti.GroupPresentation.relatorLetters_def] at h
  exact h

theorem lift_lit (w : List (Fin m0 × Bool)) : (w.map liftL).map litI = (toNw w).map litN := by
  unfold toNw
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro l _
  obtain ⟨i, b⟩ := l
  cases b <;> simp [liftL, litI, litN]

theorem any_toNw (w : List (Fin m0 × Bool)) :
    (toNw w).any (fun l => l.1 == 8) = w.any (fun l => l.1.val == 8) := by
  unfold toNw
  rw [List.any_map]
  rfl

theorem getD_toNw (i : ℕ) : (X0.map toNw).getD i [] = toNw (X0.getD i []) := by
  rw [show ([] : List (ℕ × Bool)) = toNw ([] : List (Fin m0 × Bool)) from rfl, List.getD_map]

theorem flatMap_congr' {α β : Type} {f g : α → List β} {l : List α} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  unfold List.flatMap
  rw [List.map_congr_left h]

theorem wsQ_eq : wsQ.map (fun (w : List (Fin nG × Bool)) => w.map litI) = relsQ := by
  unfold wsQ relsQ centralWords3
  rw [← x0_letters]
  simp only [List.map_append, List.map_cons, List.map_nil]
  congr 1
  · congr 1
    · rw [List.filter_map, List.map_map, List.map_map]
      have hp : ((fun w => !(w.any fun l => l.1 == 8)) ∘ toNw) =
          fun (w : List (Fin m0 × Bool)) => !(w.any fun l => l.1.val == 8) := by
        funext w
        simp only [Function.comp, any_toNw]
      rw [hp]
      apply List.map_congr_left
      intro w _
      exact lift_lit w
    · rw [getD_toNw, lift_lit]
  · rw [List.map_flatMap]
    refine flatMap_congr' fun k hk => ?_
    have hk' := List.mem_range.1 hk
    have hz1 : litI (zeta k, false) = -((12 + k : Nat) : Int) := by
      simp [litI, zeta, Fin.ofNat, Nat.mod_eq_of_lt (by omega : 11 + k < 22)]
      omega
    have hz2 : litI (zeta k, true) = ((12 + k : Nat) : Int) := by
      simp [litI, zeta, Fin.ofNat, Nat.mod_eq_of_lt (by omega : 11 + k < 22)]
      omega
    have hi : ∀ i ∈ List.range 11, (fun i => [(zeta k, true), (Fin.ofNat nG i, true), (zeta k, false),
        (Fin.ofNat nG i, false)].map litI) i =
        [((12 + k : Nat) : Int), ((i + 1 : Nat) : Int), -((12 + k : Nat) : Int), -((i + 1 : Nat) : Int)] := by
      intro i hi
      have hi' := List.mem_range.1 hi
      simp only [List.map_cons, List.map_nil, hz1, hz2]
      simp [litI, Fin.ofNat, Nat.mod_eq_of_lt (by omega : i < 22)]
    have e1 : ((X0.getD (repIdx3.getD k 0) []).map liftL ++ [(zeta k, false)]).map litI =
        ((X0.map toNw).getD (repIdx3.getD k 0) []).map litN ++ [-((12 + k : Nat) : Int)] := by
      rw [List.map_append, lift_lit, getD_toNw, List.map_cons, List.map_nil, hz1]
    have e2 : (List.replicate 9 (zeta k, true)).map litI = List.replicate 9 ((12 + k : Nat) : Int) := by
      rw [List.map_replicate, hz2]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map] at e1 ⊢
    rw [e1, e2]
    congr 1
    exact List.map_congr_left hi

end CertificateChecks.KernelRouteP

end
