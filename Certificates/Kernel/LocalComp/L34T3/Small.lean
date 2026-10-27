module

public import Certificates.Kernel.LocalComp.L34T3.Defs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5CertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34T3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34W
open CertificateChecks.KernelLC.L34X CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def tgP (k : Nat) : Nat := tgK L34R.G k

@[expose] noncomputable def h0P : Nat := pword (gS L34R.G) h0w (pidn 42 6)

@[expose] noncomputable def h0K (h : Nat) : Bool :=
  strictB h fun h => andB (Nat.beq (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) h h) h) (pidn 42 6))
    ((List.range 16).all fun k => k == 0 ||
      (notB (commPt 42 6 h (tgP k)) && notB (commPt 42 6 h (tgP (4 * k)))))

@[expose] noncomputable def z0K : Bool :=
  andB (Nat.beq (pcomp 42 6 (mask 6) (tgP 1) (tgP 16))
      (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (tgP 4) (tgP 16)) (tgP 1)))
    (Nat.beq (pcomp 42 6 (mask 6) (tgP 1) (tgP 24))
      (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (tgP 8) (tgP 24)) (tgP 1)))

@[expose] noncomputable def unitK (r : Nat) : Bool :=
  strictB r fun r => andB (commPt 42 6 r (tgP 4)) (andB (notB (commPt 42 6 r (tgP 8)))
    (andB (notB (commPt 42 6 r (tgP 12)))
      (Nat.beq (pcomp 42 6 (mask 6) r (tgP 8))
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (tgP 8) (tgP 4)) r))))

theorem k22211h : h0K h0P = true := by quickRfl

theorem k22211z : z0K = true := by quickRfl

theorem k22211u : unitK (RP 3) = true := by quickRfl

theorem kTg : andB (Nat.beq (tgP 0) (L34PT.T 0)) (andB (Nat.beq (tgP 4) (L34PT.T 5))
    (andB (Nat.beq (tgP 8) (L34PT.T 60)) (andB (Nat.beq (tgP 12) (L34PT.T 51))
      (Nat.beq (tgP 17) (L34PT.T 1))))) = true := by quickRfl

theorem k22211b : bit12OK = true := by quickRfl

end CertificateChecks.KernelLC.L34T3

end
