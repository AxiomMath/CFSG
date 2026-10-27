
module

public import Certificates.Kernel.SporSch.J4S.NoCK
meta import CFSG.Sporadic.Schreier.J4SData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.J4KV CFSG.Sporadic.J4Schreier.ksetText
#kss_tokens CertificateChecks.KernelSporSch.J4KV CFSG.Sporadic.J4Schreier.ksetText
#kss_vec CertificateChecks.KernelSporSch.J4KV.T CFSG.Sporadic.J4Schreier.ksetVectors

#ks_chars CertificateChecks.KernelSporSch.J4KE CFSG.Sporadic.J4Schreier.ksetEdgesText
#kss_tokens CertificateChecks.KernelSporSch.J4KE CFSG.Sporadic.J4Schreier.ksetEdgesText
#kss_tree CertificateChecks.KernelSporSch.J4KE.T CFSG.Sporadic.J4Schreier.ksetEdges 14

namespace CertificateChecks.KernelSporSch.J4KsK

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta
open CertificateChecks.KernelSporSch.J4NoCK

@[expose] noncomputable def UL : List Nat := List.ofFn fun j : Fin 11 => E (13 + j.val)

@[expose] noncomputable def sqK (ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun P _ ih => bAnd(Nat.beq (mulJ c rm P P) one, ih)) ps

@[expose] noncomputable def commK (P : Nat) (qs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun Q _ ih => bAnd(Nat.beq (mulJ c rm P Q) (mulJ c rm Q P), ih)) qs

@[expose] noncomputable def commsK (ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun P qs ih => bAnd(commK P qs, ih)) ps

@[expose] noncomputable def appBK (ps : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
    (fun P _ ih n v => ih (Nat.div n 2) (nIf(Nat.beq (Nat.mod n 2) 1, vecJ rm v P, v))) ps

@[expose] noncomputable def kw : Nat := vecJ rm (J4KV.T 0) (E 1)

@[expose] noncomputable def ksK (i : Nat) : Bool :=
  bIf(Nat.blt i 11385,
    bAnd(Nat.blt (J4KV.T i) (Nat.pow 2 112), bAnd(Nat.blt (ent 14 (J4KE.T i) 0) 11385,
      bAnd(Nat.beq (J4KV.T (ent 14 (J4KE.T i) 0)) (vecJ rm (J4KV.T i) (R 1)),
        bAnd(Nat.blt (ent 14 (J4KE.T i) 1) 11385,
          bAnd(Nat.beq (J4KV.T (ent 14 (J4KE.T i) 1)) (vecJ rm (J4KV.T i) (R 2)),
            notB (Nat.beq (J4KV.T i) kw)))))),
    true)

theorem root : bAnd(Nat.beq (vecJ rm rootBits (R 1)) rootBits,
    bAnd(Nat.beq (vecJ rm rootBits (R 2)) rootBits, Nat.beq (vecJ rm rootBits (E 1)) rootBits)) =
    true := by quickRfl

theorem cols : allN 11 (fun j => bAnd(
    Nat.beq (mulJ c rm (mulJ c rm (R 1) (E (Nat.add 13 j))) (R 10))
      (prodFK c rm one (ef (ent 11 J4X j))),
    Nat.beq (mulJ c rm (mulJ c rm (R 2) (E (Nat.add 13 j))) (R 11))
      (prodFK c rm one (ef (ent 11 J4Y j))))) = true := by quickRfl

theorem sq : sqK UL = true := by quickRfl
theorem comm : commsK UL = true := by quickRfl
theorem ker : allN 2047 (fun n => vneK (appBK UL (Nat.succ n) 1) 1) = true := by quickRfl

theorem pV : permsK 112 1 11385 J4KV.toks J4KV.T = true := by quickRfl
theorem pE : permsK 14 2 11385 J4KE.toks J4KE.T = true := by quickRfl

theorem ksw : Nat.blt kw (Nat.pow 2 112) = true := by quickRfl

theorem cx : Nat.beq (compK J4X J4XI) pidK = true := by quickRfl
theorem cy : Nat.beq (compK J4Y J4YI) pidK = true := by quickRfl

end CertificateChecks.KernelSporSch.J4KsK

#kss_slices CertificateChecks.KernelSporSch.J4KSV CertificateChecks.KernelSporSch.J4KsK.ksK 1024 12

end
