module

public import Certificates.Data.Kernel.L5.EngWit

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

theorem all_of_take_drop {α : Type} {f : α → Bool} {L : List α} (c : Nat)
    (h1 : (L.take c).all f = true) (h2 : (L.drop c).all f = true) : L.all f = true := by
  rw [← List.take_append_drop c L]
  simp only [List.all_append, h1, h2, Bool.and_self]

variable {n : Nat} [Group (Idx n)]

theorem allWit_of_parts (e : Eng n) (ws : List (List Nat)) (c : Nat)
    (h0 : decide (ws.length = (leaders e.reps.length).length) = true)
    (h1 : (((leaders e.reps.length).zip ws).take c).all (fun p => witOK e p.1 p.2) = true)
    (h2 : ((((leaders e.reps.length).zip ws).drop c).take c).all (fun p => witOK e p.1 p.2) = true)
    (h3 : (((((leaders e.reps.length).zip ws).drop c).drop c).take c).all
      (fun p => witOK e p.1 p.2) = true)
    (h4 : (((((leaders e.reps.length).zip ws).drop c).drop c).drop c).all
      (fun p => witOK e p.1 p.2) = true) :
    allWit e ws = true := by
  unfold allWit
  rw [h0, Bool.true_and]
  exact all_of_take_drop c h1 (all_of_take_drop c h2 (all_of_take_drop c h3 h4))

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
