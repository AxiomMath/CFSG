module

public import Certificates.Kernel.Sporadic.OddCore.Suz26990
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma44SuzCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelSpor.OddCore CFSG.EvenSporadicStandard.Solomon78
open CFSG.EvenSporadicStandard.Induction
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def e0K (n ni e1 s a b t : Nat) : Bool :=
  andB (Nat.beq (pc n (pc n n)) e) <|
    andB (notB (Nat.beq n e)) <| andB (Nat.beq (pc n a) (pc a n)) <|
    andB (Nat.beq (pc n b) (pc b n)) <| andB (Nat.beq (pc e1 e1) e) <|
    andB (Nat.beq (pc t e1) (pc e1 t)) <| andB (notB (Nat.beq e1 t)) <|
    andB (Nat.beq (pc (pc n e1) ni) (pc t e1)) <| andB (Nat.beq (pc e1 a) (pc a e1)) <|
    andB (Nat.beq (pc e1 b) (pc b e1)) <| andB (Nat.beq (pc s t) (pc t s)) <|
    notB (Nat.beq (pc s e1) (pc e1 s))

theorem k10740N : andB (lettersK 3 suzWordN) (ok (W3 suzWordN)) = true := by
  quickRfl

theorem k10740 : strictB (W3 suzWordN) (fun n => strictB (pinv n) fun ni =>
    strictB (SuzTP 0) fun t => strictB (pc (pc n t) ni) fun e1 =>
    strictB (W3 suzWordD) fun s => strictB PA fun a => strictB PB fun b =>
    e0K n ni e1 s a b t) = true := by
  quickRfl

end CertificateChecks.KernelSpor.S26990

end
