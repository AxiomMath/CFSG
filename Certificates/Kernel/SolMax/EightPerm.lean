module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.SolMaxK
public import Certificates.Data.SolMaxEightPerm
meta import Certificates.Data.SolMaxEightPerm
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSolMax.EightPerm

open CFSG.PSL3Four.Native CFSG.ComponentClassification.SolMax.SixGen
  CFSG.ComponentClassification.SolMax.EightPerm

meta def g0 : Array (Array Nat) :=
  ((eightPermCases.getD 0 default).2.1.map fun l => tabOf (permOf l)).toArray
meta def g1 : Array (Array Nat) :=
  ((eightPermCases.getD 1 default).2.1.map fun l => tabOf (permOf l)).toArray
meta def uM : Array (Array Nat) := (eightPermCases.map fun c => tabOf (permOf c.1)).toArray
meta def idM : Array Nat := idTab 9

end CertificateChecks.KernelSolMax.EightPerm

#kpenum CertificateChecks.KernelSolMax.EP0 9 4 false CertificateChecks.KernelSolMax.EightPerm.g0
  CertificateChecks.KernelSolMax.EightPerm.g0 CertificateChecks.KernelSolMax.EightPerm.idM 288
#kpenum CertificateChecks.KernelSolMax.EP1 9 4 false CertificateChecks.KernelSolMax.EightPerm.g1
  CertificateChecks.KernelSolMax.EightPerm.g1 CertificateChecks.KernelSolMax.EightPerm.idM 384
#kmisc_packarrs CertificateChecks.KernelSolMax.EightPerm.UP
  CertificateChecks.KernelSolMax.EightPerm.uM 4

namespace CertificateChecks.KernelSolMax.EightPerm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.ComponentClassification.SolMax.SixGen CFSG.ComponentClassification.SolMax.EightPerm
open CFSG.KC.SolMax
open CFSG.KLie.CT (notB)

theorem k0_hd : bAnd(gensK (gsOf (eightPermCases.getD 0 default)) 9 4 EP0.k EP0.G,
    bAnd(Nat.beq EP0.cnt (eightPermCases.getD 0 default).2.2, penumHdK (pidn 9 4) EP0.cnt
      (eightPermCases.getD 0 default).2.2 EP0.T EP0.PL)) = true := by
  quickRfl

theorem k0_sl : penumSlK 9 4 (mask 4) (9 * 4) false EP0.G EP0.GI EP0.k EP0.cnt EP0.T EP0.PL
    EP0.POS EP0.SRT EP0.SRI 0 288 = true := by
  quickRfl

theorem k0_x : bAnd(bindArrK (tabOf (permOf (eightPermCases.getD 0 default).1)) 9 4 (UP 0),
    bAnd(canonK 9 4 (mask 4) (9 * 4) (UP 0), bAnd(commK EP0.k EP0.G (UP 0),
      restZK (UP 0) EP0.cnt EP0.T))) = true := by
  quickRfl

theorem k1_hd : bAnd(gensK (gsOf (eightPermCases.getD 1 default)) 9 4 EP1.k EP1.G,
    bAnd(Nat.beq EP1.cnt (eightPermCases.getD 1 default).2.2, penumHdK (pidn 9 4) EP1.cnt
      (eightPermCases.getD 1 default).2.2 EP1.T EP1.PL)) = true := by
  quickRfl

theorem k1_sl : penumSlK 9 4 (mask 4) (9 * 4) false EP1.G EP1.GI EP1.k EP1.cnt EP1.T EP1.PL
    EP1.POS EP1.SRT EP1.SRI 0 384 = true := by
  quickRfl

theorem k1_x : bAnd(bindArrK (tabOf (permOf (eightPermCases.getD 1 default).1)) 9 4 (UP 1),
    bAnd(canonK 9 4 (mask 4) (9 * 4) (UP 1), bAnd(commK EP1.k EP1.G (UP 1),
      restZK (UP 1) EP1.cnt EP1.T))) = true := by
  quickRfl

end CertificateChecks.KernelSolMax.EightPerm

end
