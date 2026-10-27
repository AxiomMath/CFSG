module

public import Certificates.Kernel.LocalQT.He4090.L
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.H4090

open CFSG.KC.LQT.PcW

@[expose] noncomputable def famX (t : Nat) : Bool :=
  Nat.beq (rijS 8330 14 16383 (TF 0) (TF 4) (TF 5) (Nat.div (Nat.succ t) 3)
    (Nat.mod (Nat.succ t) 3)) (TF (Nat.add 16 t))

@[expose] noncomputable def famX2 (t : Nat) : Bool :=
  Nat.beq (powS 8330 14 16383 (TF 0) (TF (Nat.add 16 t)) 2) (TF (Nat.add 24 t))

@[expose] noncomputable def famC (t : Nat) : Bool :=
  distF [commS 8330 14 16383 (TF 6) (TF (Nat.add 16 t)) (TF 11) (TF (Nat.add 24 t)),
    commS 8330 14 16383 (TF 7) (TF (Nat.add 16 t)) (TF 12) (TF (Nat.add 24 t)),
    commS 8330 14 16383 (TF 8) (TF (Nat.add 16 t)) (TF 13) (TF (Nat.add 24 t)),
    commS 8330 14 16383 (TF 9) (TF (Nat.add 16 t)) (TF 14) (TF (Nat.add 24 t)),
    commS 8330 14 16383 (TF 10) (TF (Nat.add 16 t)) (TF 15) (TF (Nat.add 24 t))] []

end CFSG.KD.LQT.H4090

#kss_each CFSG.KD.LQT.H4090.X CFSG.KD.LQT.H4090.famX 8

#kss_each CFSG.KD.LQT.H4090.X2 CFSG.KD.LQT.H4090.famX2 8

#kss_each CFSG.KD.LQT.H4090.Cm CFSG.KD.LQT.H4090.famC 8

end
