module

public import Certificates.Kernel.ExcExt.Glue
public import Certificates.Kernel.ExcExt.OrbitChecks
public import Certificates.Kernel.ExcExt.InLSelChecks
public import CFSG.Certificates.Kernel.ExcExt.InLSelSound
public import CFSG.Certificates.Kernel.ExcExt.OrbitSoundP

public section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}

theorem inLSelVx_of_lineK (hK : TabsOK m K fx hx fx' hx') {Es : List KE6} {L : KLLine}
    (h : scanLineLK K Es L = true) {c : ℕ} (hcv : L.cv = c) (hc : c < 3 ^ dim m) :
    InLSelVx (excRaw m) (SelP m (e6Masks Es)) (vec m c) := by
  subst hcv
  refine inLSelVx_of_scanLineN (tabsOK_tabsK hK) (S := lsearchOf m L) ?_
  rw [code_vec m hc]
  exact scanLineLK_sound hK h

theorem inLSelVx4 (vx : V 4) : InLSelVx (excRaw 4) (SelP 4 (e6Masks S4.Es)) vx := by
  refine of_orbit tabsOK_D4 _ (fun u v h => (reflFrameAut tabsOK4 u).inLSelVx_map
      (selP_reflection tabsOK_D4 ch712516pr ch712516e6 u) h)
    (B := O.B4) (reps := [0, 1, 4, 11, 14, 416])
    (orbOK_all (w := 729) (q := 3) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · match j, hj with
    | 0, _ => exact ch712526orb4_0
    | 1, _ => exact ch712526orb4_1
    | 2, _ => exact ch712526orb4_2
    | _ + 3, h => exact absurd h (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact inLSelVx_of_lineK tabsOK_D4 ch712516l4_0 rfl (by decide)
    · exact inLSelVx_of_lineK tabsOK_D4 ch712516l4_1 rfl (by decide)
    · exact inLSelVx_of_lineK tabsOK_D4 ch712516l4_4 rfl (by decide)
    · exact inLSelVx_of_lineK tabsOK_D4 ch712516l4_11 rfl (by decide)
    · exact inLSelVx_of_lineK tabsOK_D4 ch712516l4_14 rfl (by decide)
    · exact inLSelVx_of_lineK tabsOK_D4 ch712516l4_416 rfl (by decide)

theorem inLLeafOrSelCases_four : InLLeafOrSelCases (excRaw 4) :=
  inLLeafOrSelCases_of_inLSelVx (selP_sound tabsOK_D4 ch712516e6) inLSelVx4

end CFSG.ExcExtK

end
