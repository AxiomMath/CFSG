module

public import Certificates.Data.Kernel.L34Scan2
public import Certificates.Data.Kernel.L34W.Tab42
public import Certificates.Kernel.LocalComp.L34Para.Data
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEightsCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalCertInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowCertInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34T1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan2
open CFSG.KC.L34W CertificateChecks.KernelLC.L34X
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def tgP (k : Nat) : Nat := tgK L34R.G k

@[expose] noncomputable def borelPt (NT z4 z8 z12 b : Nat) : Bool :=
  orB (memL NT L34PT.T b) (andB (notB (commPt 42 6 b z4))
    (andB (notB (commPt 42 6 b z8)) (notB (commPt 42 6 b z12))))

@[expose] noncomputable def borelK (NT : Nat) : Bool :=
  strictB (tgP 4) fun z4 => strictB (tgP 8) fun z8 => strictB (tgP 12) fun z12 =>
    allN 192 fun i => strictB (L34PB.T i) (borelPt NT z4 z8 z12)

theorem k22204 : borelK 64 = true := by quickRfl

@[expose] noncomputable def conjPt (P : Nat → Nat) (z k : Nat) (w : List Nat) : Bool :=
  strictB (pword (gS L34R.G) w (pidn 42 6)) fun x => strictB (pinvS 42 6 (mask 6) x) fun xi =>
    andB (memL 960 P x) (andB (canonK 42 6 (mask 6) (42 * 6) xi)
      (andB (Nat.beq (pcomp 42 6 (mask 6) x xi) (pidn 42 6))
        (Nat.beq (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) x (tgP k)) xi) z)))

@[expose] noncomputable def conjK (z : Nat) : Bool :=
  andB (conjP1Data.all fun d => conjPt L34P1.T z d.1 d.2)
    (conjP2Data.all fun d => conjPt L34P2.T z (4 * d.1) d.2)

theorem k22205 : strictB (tgP 4) conjK = true := by quickRfl

@[expose] noncomputable def x7P : Nat := pcomp 42 6 (mask 6) (L34R.G 0) (L34R.G 1)

@[expose] noncomputable def frobPt (x x6 u : Nat) : Bool :=
  notB (commPt 42 6 u (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) x u) x6))

@[expose] noncomputable def frobScan (x x6 : Nat) : Bool :=
  allN 315 fun i => strictB (L34O.T 0 i) (frobPt x x6)

@[expose] noncomputable def frobK (x : Nat) : Bool :=
  strictB x fun x => strictB (ppowK x 6) fun x6 =>
    andB (Nat.beq (ppowK x 7) (pidn 42 6)) (andB (notB (Nat.beq x (pidn 42 6))) (frobScan x x6))

theorem k22214 : frobK x7P = true := by quickRfl

@[expose] noncomputable def guInner (M u s : Nat) : Bool :=
  notB (allN M fun b => strictB (L34C3.P b) fun x =>
    Nat.beq (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) u x) u) s)
      (pcomp 42 6 (mask 6) s x))

@[expose] noncomputable def guPt (M r u : Nat) : Bool :=
  orB (notB (commPt 42 6 u r)) (allN 60 fun a => strictB (L34C3.P a) (guInner M u))

@[expose] noncomputable def guK (M : Nat) : Bool :=
  strictB (RP 2) fun r => allN 280 fun i => strictB (L34O.T 3 i) (guPt M r)

theorem k23331 : guK 60 = true := by quickRfl

@[expose] noncomputable def quatK (a b c : Nat) : Bool :=
  andB (Nat.beq (pcomp 42 6 (mask 6) a a) c) (andB (Nat.beq (pcomp 42 6 (mask 6) b b) c)
    (andB (Nat.beq (pcomp 42 6 (mask 6) c c) (pidn 42 6)) (andB (notB (Nat.beq c (pidn 42 6)))
      (andB (Nat.beq (pcomp 42 6 (mask 6) a b)
          (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) b c) a))
        (andB (notB (Nat.beq b (pidn 42 6))) (andB (notB (Nat.beq b a))
          (andB (notB (Nat.beq b c)) (notB (Nat.beq b (pcomp 42 6 (mask 6) c a))))))))))

theorem k22202q : (strictB (tgP 35) fun a => strictB (tgP 38) fun b => strictB (tgP 4) fun c =>
    quatK a b c) = true := by quickRfl

@[expose] noncomputable def notNormK (r4 k : Nat) : Bool :=
  strictB (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34PR.YI k) r4) (L34PR.Y k)) fun z =>
    notB (allN 4 fun i =>
      notB (notInK 64 L34PT.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) z (L34PT.G i)) z)))

@[expose] noncomputable def witPt (r4 k : Nat) (w : List Nat) : Bool :=
  strictB (pword (gS L34R.G) w (pidn 42 6)) fun c => strictB (pinvS 42 6 (mask 6) c) fun ci =>
    andB (commPt 42 6 c r4) (andB (canonK 42 6 (mask 6) (42 * 6) ci)
      (andB (Nat.beq (pcomp 42 6 (mask 6) c ci) (pidn 42 6))
        (memL 192 L34PB.T (pcomp 42 6 (mask 6) ci (L34PR.Y k)))))

@[expose] noncomputable def sylK (W : List (Nat × List Nat)) : Bool :=
  strictB (RP 3) fun r4 => allN 105 fun k =>
    orB (notNormK r4 k) (W.any fun e => andB (Nat.beq e.1 k) (witPt r4 k e.2))

theorem k22202s : sylK sylWit = true := by quickRfl

end CertificateChecks.KernelLC.L34T1

end
