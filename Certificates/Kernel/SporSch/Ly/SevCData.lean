module

public import Certificates.Kernel.SporSch.Ly.GenSeven
public import Certificates.Data.Kernel.SporSch.LySeven
public import CFSG.Certificates.Kernel.SporSch.LySevenSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.LyMatSound

public section

set_option maxRecDepth 400000

#kly_sevconj CertificateChecks.KernelSporSch.LySc 32

namespace CertificateChecks.KernelSporSch.LySc

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySev CFSG.KS.SporSch.LyM

@[expose] noncomputable def EE (i : Nat) : Nat := rowR ET 147 i

@[expose] noncomputable def SOf (i : Nat) : Nat := rowR SO 20 i

@[expose] noncomputable def SOIf (i : Nat) : Nat := rowR SOI 20 i

@[expose] noncomputable def crQ (q : Nat) : Bool :=
  bIf(Nat.blt q nS, Nat.beq (cRun KC QM ET WT PT 5 c (Nat.mul q 32) 32 (C q)) (C (Nat.succ q)), true)

@[expose] noncomputable def soQ (s : Nat) : Bool :=
  allBlk (Nat.mul s 256) (fun i => bIf(Nat.blt i c, sortB EE SOf SOIf c i, true)) 256

theorem sz : bAnd(Nat.beq c 406875, bAnd(Nat.ble c (Nat.mul nS 32), bAnd(Nat.ble nS 12736,
    bAnd(Nat.beq (C 0) 1, bAnd(Nat.beq (C nS) c, Nat.beq (rowR PT 24 0) 0))))) = true := by
  quickRfl

theorem qm : Nat.beq QM (qmK 245) = true := by quickRfl

theorem kb : allN 49 (fun t => Nat.blt (KC t) (2 ^ 4900)) = true := by quickRfl

theorem e0 : allN 49 (fun t => Nat.blt (d3 (EE 0) t) 5) = true := by quickRfl

end CertificateChecks.KernelSporSch.LySc

end
