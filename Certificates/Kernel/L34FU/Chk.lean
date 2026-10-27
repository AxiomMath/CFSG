module

public import Certificates.Kernel.L34W.Outer
public import Certificates.Kernel.L34W.Tabs
public import Certificates.Kernel.LocalComp.L34E16
public import Certificates.Kernel.LocalComp.L34RDefs
public import Certificates.Data.Kernel.L34FU
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Kernel.L34FU.Data

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelL34FU.FUW CertificateChecks.KernelL34FU.fuWit 11

#kpenum CertificateChecks.KernelL34FU.PSY 42 6 false CertificateChecks.KernelL34FU.fuPGens
  CertificateChecks.KernelL34FU.fuPGens CertificateChecks.KernelL34FU.fuId 256

namespace CertificateChecks.KernelL34FU

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34FU CFSG.KC.L34W
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X CertificateChecks.KernelL34W
open CFSG.KLie.CT (notB)

theorem ch23204_gens : bAnd(Nat.beq PSY.k 6, bAnd(allN 4 (fun j => Nat.beq (PSY.G j) (ETE.G j)),
    bAnd(Nat.beq (PSY.G 4) (L34R.G 4), Nat.beq (PSY.G 5) (L34R.G 5)))) = true := by
  quickRfl

theorem ch23204_hd : bAnd(penumHdK (pidn 42 6) PSY.cnt 256 PSY.T PSY.PL, Nat.beq PSY.cnt 256) =
    true := by
  quickRfl

theorem ch23204_sl : penumSlK 42 6 (mask 6) (42 * 6) false PSY.G PSY.GI PSY.k PSY.cnt PSY.T PSY.PL
    PSY.POS PSY.SRT PSY.SRI 0 256 = true := by
  quickRfl

theorem ch23204_exp : expK 256 PSY.T = true := by quickRfl

theorem ch23204_six : sixK T1X.F AlX.F YT (L34O.T 3) FUW (L34R.G 4) = true := by quickRfl

theorem ch23204_g4 : Nat.beq (pc (L34R.G 3) (RP 3)) (pc (RP 3) (L34R.G 3)) = true := by quickRfl

theorem ch23204n_exp : notB (expK 256 (patchT PSY.T 0 (L34R.G 3))) = true := by quickRfl

theorem ch23204n_six : notB (sixK T1X.F AlX.F YT (L34O.T 3) (fun _ => 0) (L34R.G 4)) = true := by
  quickRfl

theorem ch23204n_g4 : notB (Nat.beq (pc (L34R.G 3) (L34R.G 5)) (pc (L34R.G 5) (L34R.G 3))) =
    true := by
  quickRfl

end CertificateChecks.KernelL34FU

end
