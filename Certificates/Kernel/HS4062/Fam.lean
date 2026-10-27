module

public import Certificates.Kernel.HS4062.T
public import Certificates.Data.Kernel.LocalQT.BaseT

public section

namespace CFSG.KD.HS4062

open CFSG.KC.Kc3K

@[expose] noncomputable def appO (t c : Nat) : Nat := appS 12 4095 16 (TF t) c

@[expose] noncomputable def oRoot : Nat := packL 12 (fixE FL FM (EL 5))

@[expose] noncomputable def appZ (t c : Nat) : Nat := appP 4 15 16 (packL 4 (PI t)) c

@[expose] noncomputable def zRoot : Nat := packL 4 (List.range 16)

@[expose] noncomputable def famN (c : Nat) : Bool :=
  CFSG.KC.LQT.BT.nodesT 3850 12 progX TF (Nat.mul c 8) 8

@[expose] noncomputable def famE (c : Nat) : Bool :=
  (List.range 64).all fun t =>
    elK 12 4095 203 512 87 TF B GS eu ev ky iv kv tg (Nat.add (Nat.mul c 64) t) &&
      elQ 512 2 3 ky tg QR (Nat.add (Nat.mul c 64) t)

@[expose] noncomputable def famI (c : Nat) : Bool :=
  (List.range 32).all fun t => !decide (Nat.add (Nat.mul c 32) t < 87) ||
    (ivK 12 4095 512 87 9 TF B eu ev ky kv vu vv rt cj RI FR FL FM (Nat.add (Nat.mul c 32) t) &&
      ivX 12 4095 TF B vu vv (Nat.add (Nat.mul c 32) t))

@[expose] noncomputable def famR (c : Nat) : Bool :=
  (List.range 9).all fun t => rtK 12 4095 3850 87 TF vu vv RI FR (Nat.add (Nat.mul c 9) t)

@[expose] noncomputable def famP (c : Nat) : Bool :=
  (List.range 16).all fun t => !decide (Nat.add (Nat.mul c 16) t < 87) ||
    (prK 12 4095 87 TF B ky kv vu vv pr ct FL FM (Nat.add (Nat.mul c 16) t) &&
      nbK 87 pr NB NM (Nat.add (Nat.mul c 16) t))

@[expose] noncomputable def famS (c : Nat) : Bool :=
  (List.range 16).all fun t => !decide (Nat.add (Nat.mul c 16) t < 87) ||
    cmpK 87 pr NB NM EM (Nat.add (Nat.mul c 16) t)

@[expose] noncomputable def famO (c : Nat) : Bool :=
  (List.range 256).all fun t => !decide (Nat.add (Nat.mul c 256) t < 3850) ||
    trK 2 3850 appO OT OP oRoot (Nat.add (Nat.mul c 256) t)

@[expose] noncomputable def famZ (c : Nat) : Bool :=
  (List.range 240).all fun t => trK 3 720 appZ ZT ZP zRoot (Nat.add (Nat.mul c 240) t)

end CFSG.KD.HS4062

end
