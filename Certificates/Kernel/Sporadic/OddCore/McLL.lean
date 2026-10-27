module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
meta import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.McLCT CFSG.Sporadic.SmallOddCore.mclCentHex

#kmisc_hexflat CertificateChecks.KernelSpor.McLCT CFSG.Sporadic.SmallOddCore.mclCentHex 3 275 9 30

namespace CertificateChecks.KernelSpor.McL2287

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore
open CFSG.Sporadic.SmallOddCore.Native

meta def cInvM : Array (Array Nat) :=
  #[4, 5, 6].map fun k => CFSG.Monster.B.Co2.Native.invCand 275 (natArr (mclCentTbl k))

meta def fixM : List Nat := mclFix

meta def xgM : Array (Array Nat) := mclXGens

meta def xiM : Array (Array Nat) := mclXInvs

meta def id35 : Array Nat := idTab 35

end CertificateChecks.KernelSpor.McL2287

#kmisc_packarrs CertificateChecks.KernelSpor.McLCI CertificateChecks.KernelSpor.McL2287.cInvM 9

#knatlist CertificateChecks.KernelSpor.McL2287.fixL CertificateChecks.KernelSpor.McL2287.fixM

#kpenum CertificateChecks.KernelSpor.MXE 35 6 false CertificateChecks.KernelSpor.McL2287.xgM
  CertificateChecks.KernelSpor.McL2287.xgM CertificateChecks.KernelSpor.McL2287.id35 20160

#kmisc_packarrs CertificateChecks.KernelSpor.MXI CertificateChecks.KernelSpor.McL2287.xiM 6

namespace CertificateChecks.KernelSpor.McL2287

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Mathieu

theorem c_perm : bAnd(invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 4) (McLCI 0),
    bAnd(invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 5) (McLCI 1),
      invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 6) (McLCI 2))) = true := by
  quickRfl

theorem fix_sel : selFrom (fun x => Nat.beq (pg 9 (mask 9) (McLCT.F 4) x) x) 275 0 fixL = true := by
  quickRfl

theorem xg_ok : allN 2 (fun k => bAnd(canonK 35 6 (mask 6) (35 * 6) (MXE.G k),
    allN 35 (fun a => Nat.beq (pg 9 (mask 9) (McLCT.F (Nat.add k 5)) (nget fixL a))
      (nget fixL (pg 6 (mask 6) (MXE.G k) a))))) = true := by
  quickRfl

theorem xi_ok : allN 2 (fun k => bAnd(invEqK 35 6 (mask 6) (35 * 6) (MXE.G k) (MXI k),
    bAnd(canonK 35 6 (mask 6) (35 * 6) (MXI k),
      Nat.beq (pcomp 35 6 (mask 6) (MXI k) (MXE.G k)) (pidn 35 6)))) = true := by
  quickRfl

theorem id_ok : bAnd(canonK 35 6 (mask 6) (35 * 6) (pidn 35 6), bAnd(idK 35 6 (mask 6),
    szOK 35 6)) = true := by
  quickRfl

theorem x_hd : penumHdK (pidn 35 6) MXE.cnt 20160 MXE.T MXE.PL = true := by
  quickRfl

theorem x_sl0 : penumSlK 35 6 (mask 6) (35 * 6) false MXE.G MXE.GI MXE.k MXE.cnt MXE.T MXE.PL
    MXE.POS MXE.SRT MXE.SRI 0 5040 = true := by
  quickRfl

theorem x_sl1 : penumSlK 35 6 (mask 6) (35 * 6) false MXE.G MXE.GI MXE.k MXE.cnt MXE.T MXE.PL
    MXE.POS MXE.SRT MXE.SRI 5040 5040 = true := by
  quickRfl

theorem x_sl2 : penumSlK 35 6 (mask 6) (35 * 6) false MXE.G MXE.GI MXE.k MXE.cnt MXE.T MXE.PL
    MXE.POS MXE.SRT MXE.SRI 10080 5040 = true := by
  quickRfl

theorem x_sl3 : penumSlK 35 6 (mask 6) (35 * 6) false MXE.G MXE.GI MXE.k MXE.cnt MXE.T MXE.PL
    MXE.POS MXE.SRT MXE.SRI 15120 5040 = true := by
  quickRfl

end CertificateChecks.KernelSpor.McL2287

end
