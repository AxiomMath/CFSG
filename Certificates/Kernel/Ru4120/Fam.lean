module

public import Certificates.Kernel.Ru4120.T
public import Certificates.Data.Kernel.LocalQT.BaseT
public import Certificates.Data.Kernel.Kc3DfsK

public section

namespace CFSG.KD.Ru4120

open CFSG.KC.Kc3K

@[expose] noncomputable def famN (c : Nat) : Bool :=
  CFSG.KC.LQT.BT.nodesT 4060 12 progX TF (Nat.mul c 8) 8

@[expose] noncomputable def famE (c : Nat) : Bool :=
  (List.range 512).all fun t =>
    elK 12 4095 486 16384 687 TF B gs eu ev ky iv kv tg (Nat.add (Nat.mul c 512) t)

@[expose] noncomputable def famI (c : Nat) : Bool :=
  (List.range 64).all fun t => !decide (Nat.add (Nat.mul c 64) t < 687) ||
    ivK 12 4095 16384 687 15 TF B eu ev ky kv vu vv rt cj RI FR FL FM (Nat.add (Nat.mul c 64) t)

@[expose] noncomputable def famR : Bool :=
  (List.range 15).all fun ρ => rtK 12 4095 4060 687 TF vu vv RI FR ρ

@[expose] noncomputable def famP (c : Nat) : Bool :=
  (List.range 16).all fun t => !decide (Nat.add (Nat.mul c 16) t < 687) ||
    (prK 12 4095 687 TF B ky kv vu vv pr ct FL FM (Nat.add (Nat.mul c 16) t) &&
      nbK 687 pr NB NM (Nat.add (Nat.mul c 16) t))

@[expose] noncomputable def famS (c : Nat) : Bool :=
  dfsKR 687 pr ct NB NM (Nat.mul c 16) (min 16 (687 - Nat.mul c 16))

@[expose] noncomputable def famS0 (c : Nat) : Bool := famS c
@[expose] noncomputable def famS1 (c : Nat) : Bool := famS (Nat.add 11 c)
@[expose] noncomputable def famS2 (c : Nat) : Bool := famS (Nat.add 22 c)
@[expose] noncomputable def famS3 (c : Nat) : Bool := famS (Nat.add 33 c)

end CFSG.KD.Ru4120

end
