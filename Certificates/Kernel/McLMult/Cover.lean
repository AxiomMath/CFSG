module

public import Certificates.Kernel.McLMult.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLMult

open CFSG.F3.Native CFSG.KS.F3R CFSG.KS.F3L CFSG.KC.McLMult
  CFSG.Sporadic.Recognition.McLMultiplier

@[expose] noncomputable def yisOf (d E : Nat) (I A B B4 : V) : List V :=
  (List.range 6).map fun k => abK d E I A B B4 (invW (mclGenWord k))

@[expose] noncomputable def esOf (d E : Nat) (I : V) (Y Yi : List V) : List V :=
  (List.finRange 6).map fun i => evalK d E I (at6 Y) (at6 Yi) (mclCommWord i)

@[expose] noncomputable def eisOf (d E : Nat) (I : V) (Y Yi : List V) : List V :=
  (List.finRange 6).map fun i => evalK d E I (at6 Y) (at6 Yi) (FreeGroup.invRev (mclCommWord i))

@[expose] noncomputable def withEs {α : Type} (d : Nat) (A B : V)
    (k : Nat → V → List V → List V → α) : α :=
  strictT (spreadE d d) fun E => strictV (idLane d) fun I => strictV A fun A => strictV B fun B =>
    strictV (powLane d E I B 4) fun B4 => strictLs (ysOf d E I A B B4) fun Y =>
      strictLs (yisOf d E I A B B4) fun Yi => strictLs (esOf d E I Y Yi) fun X =>
        strictLs (eisOf d E I Y Yi) fun Xi => k E I X Xi

@[expose] noncomputable def coverAB (d : Nat) (A B : V) : Bool :=
  withEs d A B fun E I X Xi => coverCheck d E I X Xi mclRels mclCommWord mclR0

theorem seedTA_ok : seedK 42 (laneOf TA.chars) TA.chars = true := by
  decide +kernel

theorem seedTB_ok : seedK 42 (laneOf TB.chars) TB.chars = true := by
  decide +kernel

theorem id42_ok : bAnd(canonL 42 (idLane 42), eqMK 42 (idM 42) (unlane 42 (idLane 42))) = true := by
  decide +kernel

theorem cover_ok : coverAB 42 (laneOf TA.chars) (laneOf TB.chars) = true := by
  decide +kernel

end CertificateChecks.KernelMcLMult

end
