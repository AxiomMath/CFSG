module

public import CFSG.Certificates.Kernel.M24G.TrioSextsSound
public import Certificates.Kernel.M24G.ListsEq
public import Certificates.Kernel.M24G.TrioChecks
public import Certificates.Kernel.M24G.SextChecks
public import Certificates.Kernel.M24G.TSChecks

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem TL_inj (i j : Nat) (hi : i < TL.length) (hj : j < TL.length) (h : TL[i] = TL[j]) :
    i = j := by
  have hpos := (replay_facts trioReplay_ok).1
  rw [← idxK_getElem hpos 3795 hi, ← idxK_getElem hpos 3795 hj, h]

theorem trioSexts_eq : Native.trioSexts () = TS.toArray :=
  trioSexts_of_rows TrioC.length SextC.length TrioC.items SextC.items TL_inj TSC.rows
    trioList_eq sextList_eq

end CFSG.KC.M24G
