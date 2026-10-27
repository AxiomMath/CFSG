module

public import Certificates.Kernel.G24Tri.Chain27206
public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PinData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CertificateChecks.KernelG24.E8x26991

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CertificateChecks.KernelG24.Tri27206
open CFSG.EvenSporadicStandard.Induction

@[expose] noncomputable def e8S (h : Nat) : Nat := LC.S h

@[expose] noncomputable def e8SI (h : Nat) : Nat := pinvS 1365 11 (mask 11) (LC.S h)

@[expose] noncomputable def e8W (wd : List Int) : Nat :=
  CFSG.KS.Raw.wordK 1365 11 (mask 11) (pidn 1365 11) e8S e8SI wd

@[expose] noncomputable def e8M (p q : Nat) : Nat := pcomp 1365 11 (mask 11) p q

@[expose] noncomputable def e8Facts (A B C : Nat) : Bool :=
  bAnd(Nat.beq (e8M A A) (pidn 1365 11), bAnd(Nat.beq (e8M B B) (pidn 1365 11),
  bAnd(Nat.beq (e8M C C) (pidn 1365 11),
  bAnd(Nat.beq (e8M A B) (e8M B A), bAnd(Nat.beq (e8M A C) (e8M C A),
  bAnd(Nat.beq (e8M B C) (e8M C B),
  bAnd((Nat.beq A (pidn 1365 11)).not, bAnd((Nat.beq B (pidn 1365 11)).not,
  bAnd((Nat.beq B A).not, bAnd((Nat.beq C (pidn 1365 11)).not, bAnd((Nat.beq C A).not,
  bAnd((Nat.beq C B).not, (Nat.beq C (e8M A B)).not))))))))))))

theorem k26991 : bAnd(permB 1365 11 (LC.S 0), bAnd(permB 1365 11 (LC.S 1),
    strictB (e8W co1WordE1) (fun A => strictB (e8W co1WordE2) (fun B =>
      strictB (e8W co1WordE3) (fun C => e8Facts A B C))))) = true := by
  quickRfl

end CertificateChecks.KernelG24.E8x26991

end
