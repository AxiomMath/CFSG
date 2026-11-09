module

public import Certificates.Kernel.LyE81.Data
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporLyE81Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyE81

open CFSG.KD.LyE81 CFSG.RankThree.PartTwo.Sec4.Item434SporLy

@[expose] def tgD (N : Nat) (mul : Nat → Nat → Nat) (idZ : Nat) (s : List Nat) : Bool :=
  decide (81 ≤ s.length) && decide (s.Pairwise (· < ·)) &&
    s.all (fun a => decide (a < N)) && s.contains idZ &&
    s.all (fun a => (mul a (mul a a) == 0) && s.all fun b => mul a b == mul b a)

@[expose] def tgE (mul : Nat → Nat → Nat) (idZ : Nat) (sets : List (List Nat)) (i : Nat) : Bool :=
  (mul i (mul i i) != 0) || i == 0 || i == idZ || i == mul idZ idZ ||
    sets.any (fun s => s.contains i)

theorem tabG_eq (m N : Nat) (mul ed : Nat → Nat → Nat) (idZ : Nat) (sets : List (List Nat)) :
    tabG m N mul ed idZ sets = (decide (0 < idZ ∧ idZ < N) && (mul idZ (mul idZ idZ) == 0) &&
      (List.range m).all (fun k => ed idZ k == mul idZ (ed 0 k)) && sets.all (tgD N mul idZ) &&
      (List.range N).all (tgE mul idZ sets)) := rfl

theorem tabG_of {m N : Nat} {mul ed : Nat → Nat → Nat} {idZ : Nat} {sets : List (List Nat)}
    (hA : (decide (0 < idZ ∧ idZ < N) && (mul idZ (mul idZ idZ) == 0) &&
      (List.range m).all (fun k => ed idZ k == mul idZ (ed 0 k))) = true)
    (hD0 : (sets.take 1).all (tgD N mul idZ) = true) (hD1 : (sets.drop 1).all (tgD N mul idZ) = true)
    (hE : (List.range N).all (tgE mul idZ sets) = true) :
    tabG m N mul ed idZ sets = true := by
  have hD : sets.all (tgD N mul idZ) = true := by
    rw [← List.take_append_drop 1 sets, List.all_append]
    simp only [hD0, hD1, Bool.and_self]
  rw [tabG_eq]
  simp only [hA, hD, hE, Bool.and_self]

theorem tabA : (decide (0 < lyE81.idZ ∧ lyE81.idZ < 2187) &&
    (mulIdxK E PA LA 2187 lyE81.idZ (mulIdxK E PA LA 2187 lyE81.idZ lyE81.idZ) == 0) &&
    (List.range 7).all (fun k => edK E lyE81.idZ k ==
      mulIdxK E PA LA 2187 lyE81.idZ (edK E 0 k))) = true := by
  quickRfl

theorem tabD0 : (lyE81.sets.take 1).all (tgD 2187 (mulIdxK E PA LA 2187) lyE81.idZ) = true := by
  quickRfl

theorem tabD1 : (lyE81.sets.drop 1).all (tgD 2187 (mulIdxK E PA LA 2187) lyE81.idZ) = true := by
  quickRfl

theorem tabE : (List.range 2187).all (tgE (mulIdxK E PA LA 2187) lyE81.idZ lyE81.sets) = true := by
  quickRfl

theorem tab : tabG 7 2187 (mulIdxK E PA LA 2187) (edK E) lyE81.idZ lyE81.sets = true :=
  tabG_of tabA tabD0 tabD1 tabE

end CertificateChecks.KernelLyE81

end
