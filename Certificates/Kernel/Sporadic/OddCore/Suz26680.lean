module

public import Certificates.Kernel.Sporadic.OddCore.Suz26990
public import Certificates.Kernel.Sporadic.OddCore.SuzDBind
public import Certificates.Kernel.Sporadic.OddCore.SuzCT
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelSpor.S26680

meta def gM : Array (Array Nat) := CFSG.EvenSporadicStandard.Solomon78.suzTabs

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 42

end CertificateChecks.KernelSpor.S26680

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelSpor.S26680.PK 42 6 false CertificateChecks.KernelSpor.S26680.gM
  CertificateChecks.KernelSpor.S26680.gM CertificateChecks.KernelSpor.S26680.idM 20160

namespace CertificateChecks.KernelSpor.S26680

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelSpor.Suz2306
open CertificateChecks.KernelSpor.S26990 CFSG.EvenSporadicStandard.Solomon78
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def PL : Nat := W3 suzWordL

@[expose] noncomputable def PAl : Nat := pc (pc PL PA) (pinv PL)

@[expose] noncomputable def PBl : Nat := pc (pc PL PB) (pinv PL)

@[expose] noncomputable def PZ : Nat := WK suzWordZ

@[expose] noncomputable def sel4 (a b c d j : Nat) : Nat :=
  nIf(Nat.beq j 0, a, nIf(Nat.beq j 1, b, nIf(Nat.beq j 2, c, d)))

@[expose] noncomputable def W4 (w : List Int) : Nat :=
  wordK 1782 11 (mask 11) e (sel4 PA PB PAl PBl) (sel4 (pinv PA) (pinv PB) (pinv PAl) (pinv PBl)) w

@[expose] noncomputable def res (p : Nat) : Nat := CFSG.KC.PermTool.restrictK 11 6 SuzD.fixL0 p

@[expose] noncomputable def fixN (p : Nat) : Nat :=
  ((List.range 1782).filter fun x => Nat.beq (pg 11 (mask 11) p x) x).length

theorem kLet : andB (lettersK 3 suzWordL) (andB (lettersK 2 suzWordZ)
    (andB (lettersK 4 suzWordG0) (lettersK 4 suzWordG1))) = true := by
  quickRfl

theorem kInv : andB (ok PL) (andB (ok PAl) (andB (ok PBl) (andB (cn PZ)
    (andB (cn B0) (cn B1))))) = true := by
  quickRfl

theorem kRel : andB (Nat.beq (ppow 1782 11 (mask 11) e PA 3) e)
    (andB (Nat.beq (ppow 1782 11 (mask 11) e PB 3) e)
    (andB (Nat.beq (SuzTP 0) B0)
    (andB (Nat.beq (pc PA (SuzTP 0)) (pc (SuzTP 0) PA))
    (andB (Nat.beq (pc PB (SuzTP 0)) (pc (SuzTP 0) PB))
    (andB (Nat.beq (pc (pc PL (SuzTP 0)) (pinv PL)) (pc (SuzTP 0) PZ))
    (andB (Nat.beq (W4 suzWordG0) B0)
    (andB (Nat.beq (W4 suzWordG1) B1)
      (Nat.beq (pc PZ PZ) e)))))))) = true := by
  quickRfl

theorem kFix : Nat.beq (fixN PZ) 54 = true := by quickRfl

theorem kRes : andB (canonK 42 6 (mask 6) (42 * 6) (res PA))
    (andB (canonK 42 6 (mask 6) (42 * 6) (res PB))
    (andB (canonK 42 6 (mask 6) (42 * 6) (res PZ))
      (notB (Nat.beq (res PZ) (pidn 42 6))))) = true := by
  quickRfl

theorem kCls : allN 10 (fun l => orB (Nat.beq l 0) (orB (Nat.beq l 6)
    (notB (Nat.beq (pcomp 42 6 (mask 6) (SuzCT.OF.R l) (SuzCT.OF.R l)) (pidn 42 6))))) = true := by
  quickRfl

theorem kHd : andB (Nat.beq PK.cnt 20160) (andB (Nat.beq PK.k 2)
    (andB (penumHdK (pidn 42 6) PK.cnt 20160 PK.T PK.PL)
      (andB (Nat.beq (PK.G 0) (res PA)) (Nat.beq (PK.G 1) (res PB))))) = true := by
  quickRfl

theorem kNeg : andB (notB (Nat.beq (fixN PZ) 42)) (notB (Nat.beq (pc PZ PA) (pc PA PZ))) = true := by
  quickRfl

@[expose] noncomputable def kSl (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false PK.G PK.GI 2 PK.cnt PK.T PK.PL PK.POS PK.SRT
    PK.SRI (Nat.mul s (nat_lit 1260)) (nat_lit 1260)

end CertificateChecks.KernelSpor.S26680

end
