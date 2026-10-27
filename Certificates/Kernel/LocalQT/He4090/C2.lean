module

public import Certificates.Kernel.LocalQT.He4090.L
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.H4090

open CFSG.KC.Enum CFSG.KC.LQT.PcW CFSG.QuasithinUnique.Vol2Native.L239.HePairs
open CFSG.QuasithinUnique.Ch1.SporLat.He

theorem r1 : Nat.beq (qtW 8330 14 16383 (TF 0) L2c r2a.w r2a.k) (TF 4) = true := by
  quickRfl

theorem r2 : Nat.beq (qtW 8330 14 16383 (TF 0) L2c r2b.w r2b.k) (TF 5) = true := by
  quickRfl

theorem r1ne : neB (TF 4) (TF 0) = true := by
  quickRfl

theorem r2ne : neB (TF 5) (TF 0) = true := by
  quickRfl

theorem r1c : Nat.beq (powS 8330 14 16383 (TF 0) (TF 4) 3) (TF 0) = true := by
  quickRfl

theorem r2c : Nat.beq (powS 8330 14 16383 (TF 0) (TF 5) 3) (TF 0) = true := by
  quickRfl

theorem rcm : Nat.beq (pcS 8330 14 16383 (TF 4) (TF 5)) (pcS 8330 14 16383 (TF 5) (TF 4)) = true := by
  quickRfl

theorem r21 : neB (TF 5) (TF 4) = true := by
  quickRfl

theorem r212 : neB (TF 5) (powS 8330 14 16383 (TF 0) (TF 4) 2) = true := by
  quickRfl

@[expose] noncomputable def famQT (k : Nat) : Bool :=
  Nat.beq (qtW 8330 14 16383 (TF 0) L2c (nthQ q2s k).w (nthQ q2s k).k) (TF (Nat.add 6 k))

@[expose] noncomputable def famQI (k : Nat) : Bool :=
  Nat.beq (powS 8330 14 16383 (TF 0) (TF (Nat.add 6 k)) (Nat.sub (nthQ q2s k).m 1))
    (TF (Nat.add 11 k))

@[expose] noncomputable def famQM (k : Nat) : Bool :=
  Nat.beq (powS 8330 14 16383 (TF 0) (TF (Nat.add 6 k)) (nthQ q2s k).m) (TF 0)

@[expose] noncomputable def famQL (k : Nat) : Bool :=
  labsK 8330 14 16383 (TF (Nat.add 6 k)) heLabels2

end CFSG.KD.LQT.H4090

#kss_each CFSG.KD.LQT.H4090.QT CFSG.KD.LQT.H4090.famQT 5

#kss_each CFSG.KD.LQT.H4090.QI CFSG.KD.LQT.H4090.famQI 5

#kss_each CFSG.KD.LQT.H4090.QM CFSG.KD.LQT.H4090.famQM 5

#kss_each CFSG.KD.LQT.H4090.QL CFSG.KD.LQT.H4090.famQL 5

end
