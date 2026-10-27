module

public import Certificates.Kernel.SporSch.Tits.Inv2266D
public import Certificates.Kernel.SporSch.Tits.GenMask
public import CFSG.Certificates.Kernel.SporSch.TitsCntSound
public import Certificates.Kernel.Sporadic.Tits.LocN
public import Certificates.Kernel.Sporadic.Tits.LocK
meta import CFSG.Sporadic.Schreier.TitsInvCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kst_mask CertificateChecks.KernelSporSch.TitsMH CFSG.Sporadic.Schreier.Tits.titsHLevels
  CFSG.Sporadic.Schreier.Tits.titsTArr
#kst_maskN CertificateChecks.KernelSporSch.TitsMN CFSG.Sporadic.Schreier.Tits.titsNLevels
  CFSG.Sporadic.Schreier.Tits.titsTArr CFSG.Sporadic.Schreier.Tits.inK

namespace CertificateChecks.KernelSporSch.TitsInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

@[expose] noncomputable def PTH (t0 t1 t2 t3 t4 : Nat) : Bool :=
  baseComm TitsH.BP 5 (gptR t0 t1 t2 t3 t4) (pgR TitsT)

@[expose] noncomputable def PTN (t0 t1 t2 t3 t4 : Nat) : Bool :=
  baseComm TitsN.BP 5 (gptR t0 t1 t2 t3 t4) (pgR TitsT)

@[expose] noncomputable def PK (t0 t1 t2 t3 t4 : Nat) : Bool :=
  bAnd(PTN t0 t1 t2 t3 t4, ktKB TitsK.LR TitsK.TRI TitsK.BP TitsN.BP t0 t1 t2 t3 t4)

@[expose] noncomputable def PC (t0 t1 t2 t3 t4 : Nat) : Bool :=
  bAnd(PTN t0 t1 t2 t3 t4, ctKG TitsN.BP TitsN.LR TitsN.TR TitsMN.GC t0 t1 t2 t3 t4)

@[expose] noncomputable def QHt : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ PTH TitsMH.M
@[expose] noncomputable def QNt : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ PTN TitsMN.M
@[expose] noncomputable def QNk : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ PK TitsMN.MK
@[expose] noncomputable def QNc : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ PC TitsMN.MC


theorem cntH : Nat.beq (popc (tot5 TitsH.LR) TitsMH.M) 512 = true := by quickRfl
theorem cntN : Nat.beq (popc (tot5 TitsN.LR) TitsMN.M) 1536 = true := by quickRfl
theorem cntK : Nat.beq (popc (tot5 TitsN.LR) TitsMN.MK) 256 = true := by quickRfl
theorem cntC : Nat.beq (popc (tot5 TitsN.LR) TitsMN.MC) 8 = true := by quickRfl
theorem mK : Nat.beq (maskOf TitsMN.CK) TitsMN.MK = true := by quickRfl
theorem aK : ascK (tot5 TitsN.LR) TitsMN.CK 0 = true := by quickRfl
theorem subCK : Nat.beq (Nat.land TitsMN.MC TitsMN.MK) TitsMN.MC = true := by quickRfl

theorem kTH : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsH.LR TitsH.TRI TitsH.BP 5 0 TitsT =
    true := by quickRfl
theorem kTN : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0 TitsT =
    true := by quickRfl
theorem kKN : allN 7 (fun j => siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI
    TitsN.BP 5 0 (TitsK.S j)) = true := by quickRfl
theorem canK : allN 7 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsK.S j)) = true := by
  quickRfl
theorem kTree : qtreeK TitsN.BP TitsN.LR TitsN.TR TitsMN.GC TitsMN.CK TitsMN.W = true := by quickRfl

theorem canTRH : allN 5 (fun i => allN (rcnt (TitsH.LR i)) (fun a =>
    canonK 1755 11 (mask 11) (1755 * 11) (trAt 1755 (1755 * 11) TitsH.LR TitsH.TR i a))) = true := by
  quickRfl
theorem canTRN : allN 5 (fun i => allN (rcnt (TitsN.LR i)) (fun a =>
    canonK 1755 11 (mask 11) (1755 * 11) (trAt 1755 (1755 * 11) TitsN.LR TitsN.TR i a))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.TitsInv

end
