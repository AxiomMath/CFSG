module

public import Certificates.Kernel.HeDc.Defs
public import Certificates.Data.Kernel.SporLatDcL
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.HeDc

open CFSG.KC.SLDc

theorem glob : globalOK C D = true := by
  quickRfl

theorem pts : (List.range D.npc).all (ptChunk C D) = true := by
  quickRfl

theorem orbs : (List.range D.obase.length).all (orbOK C D) = true := by
  quickRfl

@[expose] noncomputable def memOKL (j : Nat) : Bool :=
  omOKL (fun l x => labF (Lm j l) x) Δ (Nat.add 4 (J.mw.getD j []).length) (Om j) &&
    omOKL (fun l X => X.map (labF (L (Nat.add 2 l)))) (Om j).lbl.toList 4 (Ot j)

theorem mems : (List.range 11).all memOK = true := by
  have e : memOK = memOKL := by
    funext j
    rw [memOK, memOKL, omOKL_eq]
  rw [e]
  quickRfl

theorem incl : inclOK = true := by
  quickRfl

theorem invs : (List.range 4).all (fun i => (List.range 8330).all fun p =>
    L (Nat.add 6 i) (L (Nat.add 2 i) p) == p) = true := by
  quickRfl

end CFSG.KD.HeDc

end
