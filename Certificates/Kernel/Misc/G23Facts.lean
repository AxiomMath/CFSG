module

public import CFSG.Certificates.Kernel.Misc.G23Sound
public import Certificates.Kernel.Misc.G23Checks

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.G23

open CFSG.KC.Misc CFSG.KC.Misc.G24 CFSG.KC.Misc.G23 CFSG.LieType.Multipliers.G23

theorem bA : atlasA = CFSG.KC.Misc.G24.strOf cA := rfl
theorem bB : atlasB = CFSG.KC.Misc.G24.strOf cB := rfl
theorem toList_rep (k : ℕ) (s : String) :
    (rep k s).toList = (List.replicate k s.toList).flatten := by
  rw [rep, String.toList_join]
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem bR : rels.map encW = Rc := by
  simp only [rels, relStrings, relSixString, List.map, parseWord, toList_rep, String.toList_append]
  decide +kernel
theorem bP : ∀ i : Fin 2, (pairs i).map (fun p => (encW p.1, encW p.2)) = nthP Pc i := by
  decide +kernel
theorem bW : encW relSix = six := by
  simp only [relSix, relSixString, parseWord, toList_rep, String.toList_append]
  decide +kernel

theorem facts : coverCheck = true ∧ relSixCheck = true := by
  rw [CFSG.KC.Misc.G23.coverCheck_eq, CFSG.KC.Misc.G23.relSixCheck_eq]
  exact g23_sound bA bB (fun _ => rfl) rfl rfl bR bP bW check

end CFSG.KD.Misc.G23

end
