
module

public import Certificates.Kernel.SporSch.J4S.FiveT
public import CFSG.Sporadic.Schreier.J4SInvData
public import Certificates.Data.Kernel.J4Q.Mat
public import CFSG.Certificates.Kernel.SporSch.J4STextSound
meta import CFSG.Sporadic.Schreier.J4SInvData
meta import Certificates.Kernel.SporSch.J4S.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.J4IF CFSG.Sporadic.J4Schreier.invForestText
#kss_tokens CertificateChecks.KernelSporSch.J4IF CFSG.Sporadic.J4Schreier.invForestText
#kss_tree CertificateChecks.KernelSporSch.J4IF.T CFSG.Sporadic.J4Schreier.invForest 15

#ks_chars CertificateChecks.KernelSporSch.J4IC CFSG.Sporadic.J4Schreier.invConjText
#kss_tokens CertificateChecks.KernelSporSch.J4IC CFSG.Sporadic.J4Schreier.invConjText
#kss_tree CertificateChecks.KernelSporSch.J4IC.T CFSG.Sporadic.J4Schreier.conjTab 10

#ks_chars CertificateChecks.KernelSporSch.J4AH CFSG.Sporadic.J4Schreier.ambText
#kss_tokens CertificateChecks.KernelSporSch.J4AH CFSG.Sporadic.J4Schreier.ambText
#kss_tree CertificateChecks.KernelSporSch.J4AH.T CFSG.Sporadic.J4Schreier.ambHead 11

#ks_chars CertificateChecks.KernelSporSch.J4AW CFSG.Sporadic.J4Schreier.ambWordsText
#kss_tokens CertificateChecks.KernelSporSch.J4AW CFSG.Sporadic.J4Schreier.ambWordsText
#kss_words CertificateChecks.KernelSporSch.J4AW CFSG.Sporadic.J4Schreier.ambWordsText 77

#kss_table CertificateChecks.KernelSporSch.J4GI CFSG.Sporadic.J4Schreier.genInvColumns 11 11
#kss_tree CertificateChecks.KernelSporSch.J4FW2 CertificateChecks.KernelSporSch.J4Inv.forestW 15

namespace CertificateChecks.KernelSporSch.J4InvC

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KC.J4Q
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch

@[expose] noncomputable def FF (k j : Nat) : Nat := ent 15 (J4IF.T j) k

@[expose] noncomputable def CT (i e : Nat) : Nat := ent 10 (J4IC.T i) e

@[expose] noncomputable def AH (k i : Nat) : Nat := ent 11 (J4AH.T i) k

@[expose] noncomputable def anyK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) n

@[expose] noncomputable def ambK (n e : Nat) : Bool :=
  anyK 77 (fun i => bAnd(Nat.beq (AH 0 i) n, Nat.beq (AH 1 i) e))

@[expose] noncomputable def fixK (n e : Nat) : Bool :=
  bAnd(Nat.beq (J4SQ.T e) 0, bAnd(Nat.beq (appK (J4E.T e) n) n,
    notB (bAnd(Nat.beq n 0, Nat.beq e 0))))

@[expose] noncomputable def gN (g n e : Nat) : Nat :=
  nIf(Nat.beq g 0, Nat.xor (Nat.xor n 4) (appK (J4E.T e) 4), appK (J4GC (Nat.sub g 1)) n)

@[expose] noncomputable def gE (g e : Nat) : Nat := nIf(Nat.beq g 0, e, CT (Nat.sub g 1) e)

@[expose] noncomputable def recK (j : Nat) : Bool :=
  bIf(Nat.blt j 19967,
    bAnd(Nat.blt (FF 0 j) 2048, bAnd(Nat.blt (FF 1 j) 1024, bAnd(fixK (FF 0 j) (FF 1 j),
      bIf(Nat.beq (FF 2 j) j, bIf(Nat.beq (FF 1 j) 0, true, ambK (FF 0 j) (FF 1 j)),
        bAnd(Nat.blt (FF 2 j) j, bAnd(Nat.blt (FF 3 j) 5, bAnd(Nat.blt (FF 1 (FF 2 j)) 1024,
          bAnd(Nat.beq (gN (FF 3 j) (FF 0 (FF 2 j)) (FF 1 (FF 2 j))) (FF 0 j),
            Nat.beq (gE (FF 3 j) (FF 1 (FF 2 j))) (FF 1 j))))))))),
    true)

@[expose] noncomputable def WI (n e : Nat) : Nat := ent 15 (J4FW2 e) n

@[expose] noncomputable def idxK (e : Nat) : Bool :=
  bIf(bAnd(Nat.blt e 1024, Nat.beq (J4SQ.T e) 0),
    allN 2048 (fun n => bIf(fixK n e,
      bAnd(Nat.blt (WI n e) 19967, bAnd(Nat.beq (FF 0 (WI n e)) n, Nat.beq (FF 1 (WI n e)) e)),
      true)),
    true)

@[expose] noncomputable def conjK (i e : Nat) : Bool :=
  bAnd(Nat.blt (CT i e) 1024,
    Nat.beq (J4E.T (CT i e)) (compK (compK (J4GC i) (J4E.T e)) (J4GI i)))

@[expose] noncomputable def parK (e : Nat) : Bool :=
  bIf(bAnd(Nat.blt 0 e, Nat.blt (ent 10 (J4D.T e) 0) e), Nat.blt (ent 10 (J4D.T e) 1) 4, true)

theorem pF : permsK 15 4 19967 J4IF.toks J4IF.T = true := by quickRfl
theorem pC : permsK 10 1024 4 J4IC.toks J4IC.T = true := by quickRfl
theorem pA : permsK 11 3 77 J4AH.toks J4AH.T = true := by quickRfl

theorem gi : allN 4 (fun i => Nat.beq (compK (J4GC i) (J4GI i)) pidK) = true := by quickRfl
theorem conj0 : allN 1024 (conjK 0) = true := by quickRfl
theorem conj1 : allN 1024 (conjK 1) = true := by quickRfl
theorem conj2 : allN 1024 (conjK 2) = true := by quickRfl
theorem conj3 : allN 1024 (conjK 3) = true := by quickRfl
theorem ah : allN 77 (fun i => bAnd(Nat.blt (AH 0 i) 2048, bAnd(Nat.blt (AH 1 i) 1024,
    bIf(Nat.beq (AH 2 i) 1, true, Nat.beq (AH 2 i) 14)))) = true := by quickRfl
theorem par : allN 1024 parK = true := by quickRfl

end CertificateChecks.KernelSporSch.J4InvC

#kss_slices CertificateChecks.KernelSporSch.J4IR CertificateChecks.KernelSporSch.J4InvC.recK 1024 20
#kss_slices CertificateChecks.KernelSporSch.J4IX CertificateChecks.KernelSporSch.J4InvC.idxK 64 16

end
