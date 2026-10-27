module

public import Certificates.Kernel.McLMult.Data
public import Certificates.Data.Kernel.McLMultK
public import CFSG.Certificates.Kernel.Spor.F3R

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLMult

open CFSG.F3.Native CFSG.KS.F3R CFSG.KS.F3L CFSG.KC.McLMult
  CFSG.Sporadic.Recognition.McLMultiplier

@[expose] noncomputable def ysOf (d E : Nat) (I A B B4 : V) : List V :=
  (List.range 6).map fun k => abK d E I A B B4 (mclGenWord k)

@[expose] noncomputable def genAB (d : Nat) (A B : V) : Bool :=
  strictT (spreadE d d) fun E => strictV (idLane d) fun I => strictV A fun A => strictV B fun B =>
    strictV (powLane d E I B 4) fun B4 => strictLs (ysOf d E I A B B4) fun Y =>
      genCheck d E I A B Y mclRels mclCommWord mclSurjA mclSurjB

theorem seedA_ok : seedK 21 (laneOf SA.chars) SA.chars = true := by
  decide +kernel

theorem seedB_ok : seedK 21 (laneOf SB.chars) SB.chars = true := by
  decide +kernel

theorem id21_ok : bAnd(canonL 21 (idLane 21), eqMK 21 (idM 21) (unlane 21 (idLane 21))) = true := by
  decide +kernel

theorem gen_ok : genAB 21 (laneOf SA.chars) (laneOf SB.chars) = true := by
  decide +kernel

end CertificateChecks.KernelMcLMult

end
