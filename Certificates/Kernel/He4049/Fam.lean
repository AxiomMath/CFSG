module

public import Certificates.Kernel.He4049.T
public import Certificates.Data.Kernel.LocalQT.BaseT
public import Certificates.Data.Kernel.Kc3DfsK

public section

namespace CFSG.KD.He4049

open CFSG.KC.Kc3K

@[expose] noncomputable def famN (c : Nat) : Bool :=
  CFSG.KC.LQT.BT.nodesT 8330 14 progX TF (Nat.mul c 8) 8

@[expose] noncomputable def famE (c : Nat) : Bool :=
  (List.range 128).all fun t =>
    elK 14 16383 343 1024 191 TF B gs eu ev ky iv kv tg (Nat.add (Nat.mul c 128) t)

@[expose] noncomputable def famI (c : Nat) : Bool :=
  (List.range 32).all fun t => !decide (Nat.add (Nat.mul c 32) t < 191) ||
    ivK 14 16383 1024 191 25 TF B eu ev ky kv vu vv rt cj RI FR FL FM (Nat.add (Nat.mul c 32) t)

@[expose] noncomputable def famR (c : Nat) : Bool :=
  (List.range 5).all fun t => rtK 14 16383 8330 191 TF vu vv RI FR (Nat.add (Nat.mul c 5) t)

@[expose] noncomputable def famP (c : Nat) : Bool :=
  (List.range 16).all fun t => !decide (Nat.add (Nat.mul c 16) t < 191) ||
    (prK 14 16383 191 TF B ky kv vu vv pr ct FL FM (Nat.add (Nat.mul c 16) t) &&
      nbK 191 pr NB NM (Nat.add (Nat.mul c 16) t))

@[expose] noncomputable def famS (c : Nat) : Bool :=
  dfsKR 191 pr ct NB NM (Nat.mul c 16) (min 16 (191 - Nat.mul c 16))

end CFSG.KD.He4049

end
