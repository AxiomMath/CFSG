module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.SolMaxK
public import Certificates.Data.SolMaxThreeCent
meta import Certificates.Data.SolMaxThreeCent
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSolMax.ThreeCent

open CFSG.PSL3Four.Native CFSG.ComponentClassification.SolMax.SixGen
  CFSG.ComponentClassification.SolMax.ThreeCent

meta def g0 : Array (Array Nat) :=
  ((threeCentCases.getD 0 default).2.1.map fun l => tabOf (permOf l)).toArray
meta def g1 : Array (Array Nat) :=
  ((threeCentCases.getD 1 default).2.1.map fun l => tabOf (permOf l)).toArray
meta def g2 : Array (Array Nat) :=
  ((threeCentCases.getD 2 default).2.1.map fun l => tabOf (permOf l)).toArray
meta def uM : Array (Array Nat) := (threeCentCases.map fun c => tabOf (permOf c.1)).toArray
meta def negM : Array (Array Nat) := #[tabOf (permOf [(0, 1), (0, 2), (0, 3), (4, 5), (4, 6), (4, 7)])]
meta def idM : Array Nat := idTab 9

end CertificateChecks.KernelSolMax.ThreeCent

#kpenum CertificateChecks.KernelSolMax.TC0 9 4 false CertificateChecks.KernelSolMax.ThreeCent.g0
  CertificateChecks.KernelSolMax.ThreeCent.g0 CertificateChecks.KernelSolMax.ThreeCent.idM 2160
#kpenum CertificateChecks.KernelSolMax.TC1 9 4 false CertificateChecks.KernelSolMax.ThreeCent.g1
  CertificateChecks.KernelSolMax.ThreeCent.g1 CertificateChecks.KernelSolMax.ThreeCent.idM 108
#kpenum CertificateChecks.KernelSolMax.TC2 9 4 false CertificateChecks.KernelSolMax.ThreeCent.g2
  CertificateChecks.KernelSolMax.ThreeCent.g2 CertificateChecks.KernelSolMax.ThreeCent.idM 162
#kmisc_packarrs CertificateChecks.KernelSolMax.ThreeCent.UP
  CertificateChecks.KernelSolMax.ThreeCent.uM 4
#kmisc_packarrs CertificateChecks.KernelSolMax.ThreeCent.NP
  CertificateChecks.KernelSolMax.ThreeCent.negM 4

namespace CertificateChecks.KernelSolMax.ThreeCent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.ComponentClassification.SolMax.SixGen CFSG.ComponentClassification.SolMax.ThreeCent
open CFSG.KC.SolMax
open CFSG.KLie.CT (notB)

theorem k0_hd : bAnd(gensK (gsOf (threeCentCases.getD 0 default)) 9 4 TC0.k TC0.G,
    bAnd(Nat.beq TC0.cnt (threeCentCases.getD 0 default).2.2, penumHdK (pidn 9 4) TC0.cnt
      (threeCentCases.getD 0 default).2.2 TC0.T TC0.PL)) = true := by
  quickRfl

theorem k0_sl : penumSlK 9 4 (mask 4) (9 * 4) false TC0.G TC0.GI TC0.k TC0.cnt TC0.T TC0.PL
    TC0.POS TC0.SRT TC0.SRI 0 2160 = true := by
  quickRfl

theorem k0_x : bAnd(bindArrK (tabOf (permOf (threeCentCases.getD 0 default).1)) 9 4 (UP 0),
    bAnd(canonK 9 4 (mask 4) (9 * 4) (UP 0), bAnd(commK TC0.k TC0.G (UP 0),
    bAnd(restXK TC0.cnt TC0.T, restYK TC0.cnt TC0.T)))) = true := by
  quickRfl

theorem k1_hd : bAnd(gensK (gsOf (threeCentCases.getD 1 default)) 9 4 TC1.k TC1.G,
    bAnd(Nat.beq TC1.cnt (threeCentCases.getD 1 default).2.2, penumHdK (pidn 9 4) TC1.cnt
      (threeCentCases.getD 1 default).2.2 TC1.T TC1.PL)) = true := by
  quickRfl

theorem k1_sl : penumSlK 9 4 (mask 4) (9 * 4) false TC1.G TC1.GI TC1.k TC1.cnt TC1.T TC1.PL
    TC1.POS TC1.SRT TC1.SRI 0 108 = true := by
  quickRfl

theorem k1_x : bAnd(bindArrK (tabOf (permOf (threeCentCases.getD 1 default).1)) 9 4 (UP 1),
    bAnd(canonK 9 4 (mask 4) (9 * 4) (UP 1), bAnd(commK TC1.k TC1.G (UP 1),
    bAnd(restXK TC1.cnt TC1.T, restYK TC1.cnt TC1.T)))) = true := by
  quickRfl

theorem k2_hd : bAnd(gensK (gsOf (threeCentCases.getD 2 default)) 9 4 TC2.k TC2.G,
    bAnd(Nat.beq TC2.cnt (threeCentCases.getD 2 default).2.2, penumHdK (pidn 9 4) TC2.cnt
      (threeCentCases.getD 2 default).2.2 TC2.T TC2.PL)) = true := by
  quickRfl

theorem k2_sl : penumSlK 9 4 (mask 4) (9 * 4) false TC2.G TC2.GI TC2.k TC2.cnt TC2.T TC2.PL
    TC2.POS TC2.SRT TC2.SRI 0 162 = true := by
  quickRfl

theorem k2_x : bAnd(bindArrK (tabOf (permOf (threeCentCases.getD 2 default).1)) 9 4 (UP 2),
    bAnd(canonK 9 4 (mask 4) (9 * 4) (UP 2), bAnd(commK TC2.k TC2.G (UP 2),
    bAnd(restXK TC2.cnt TC2.T, restYK TC2.cnt TC2.T)))) = true := by
  quickRfl

theorem k_neg : notB (restXK 1 fun _ => NP 0) = true := by
  quickRfl

end CertificateChecks.KernelSolMax.ThreeCent

end
