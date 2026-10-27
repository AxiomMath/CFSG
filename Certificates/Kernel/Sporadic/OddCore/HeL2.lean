module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SmallOddCore.HeLocalCheck2Inputs
meta import CFSG.Sporadic.SmallOddCore.HeLocalCheck2Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He2276

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.HeldB

meta def xM : Array (Array Nat) := heXTabs

meta def xiM : Array (Array Nat) := heXInvs

meta def rM : Array (Array Nat) := heRGens

meta def id42 : Array Nat := idTab 42

meta def normPosM (first : Bool) : Array (Array Nat) :=
  let idx := indexOf heREnum.tabs
  ((List.range 9).toArray.map fun j => (List.range 6).toArray.map fun i =>
    let x := if first then conjTab 42 heXTabs[j]! heXInvs[j]! heRGens[i]!
      else conjTab 42 heXInvs[j]! heXTabs[j]! heRGens[i]!
    #[idx.getD x 0]).flatten

meta def normPos1M : Array (Array Nat) := normPosM true

meta def normPos2M : Array (Array Nat) := normPosM false

end CertificateChecks.KernelSpor.He2276

#kpenum CertificateChecks.KernelSpor.HXE 42 6 false CertificateChecks.KernelSpor.He2276.xM
  CertificateChecks.KernelSpor.He2276.xM CertificateChecks.KernelSpor.He2276.id42 10752

#kpenum CertificateChecks.KernelSpor.HRE 42 6 false CertificateChecks.KernelSpor.He2276.rM
  CertificateChecks.KernelSpor.He2276.rM CertificateChecks.KernelSpor.He2276.id42 64

#kmisc_packarrs CertificateChecks.KernelSpor.HXI CertificateChecks.KernelSpor.He2276.xiM 6

#kmisc_packarrs CertificateChecks.KernelSpor.He2276.HNP1
  CertificateChecks.KernelSpor.He2276.normPos1M 32

#kmisc_packarrs CertificateChecks.KernelSpor.He2276.HNP2
  CertificateChecks.KernelSpor.He2276.normPos2M 32

namespace CertificateChecks.KernelSpor.He2276

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

theorem x_gens : gensK heXTabs 42 6 HXE.k HXE.G = true := by
  quickRfl

theorem x_perm : allN 9 (fun j => bAnd(invEqK 42 6 (mask 6) (42 * 6) (HXE.G j) (HXI j),
    bAnd(invEqK 42 6 (mask 6) (42 * 6) (HXI j) (HXE.G j),
    bAnd(canonK 42 6 (mask 6) (42 * 6) (HXI j),
      Nat.beq (pcomp 42 6 (mask 6) (HXI j) (HXE.G j)) (pidn 42 6))))) = true := by
  quickRfl

theorem id_ok : bAnd(canonK 42 6 (mask 6) (42 * 6) (pidn 42 6), bAnd(idK 42 6 (mask 6),
    szOK 42 6)) = true := by
  quickRfl

theorem x_hd : penumHdK (pidn 42 6) HXE.cnt 10752 HXE.T HXE.PL = true := by
  quickRfl

theorem x_sl0 : penumSlK 42 6 (mask 6) (42 * 6) false HXE.G HXE.GI HXE.k HXE.cnt HXE.T HXE.PL
    HXE.POS HXE.SRT HXE.SRI 0 2688 = true := by
  quickRfl

theorem x_sl1 : penumSlK 42 6 (mask 6) (42 * 6) false HXE.G HXE.GI HXE.k HXE.cnt HXE.T HXE.PL
    HXE.POS HXE.SRT HXE.SRI 2688 2688 = true := by
  quickRfl

theorem x_sl2 : penumSlK 42 6 (mask 6) (42 * 6) false HXE.G HXE.GI HXE.k HXE.cnt HXE.T HXE.PL
    HXE.POS HXE.SRT HXE.SRI 5376 2688 = true := by
  quickRfl

theorem x_sl3 : penumSlK 42 6 (mask 6) (42 * 6) false HXE.G HXE.GI HXE.k HXE.cnt HXE.T HXE.PL
    HXE.POS HXE.SRT HXE.SRI 8064 2688 = true := by
  quickRfl

theorem r_gens : allN 6 (fun j => bAnd(Nat.beq (HRE.G j)
    (wordTabK 42 6 (mask 6) (pidn 42 6) HXE.G (lget2 heRWords j)),
    canonK 42 6 (mask 6) (42 * 6) (HRE.G j))) = true := by
  quickRfl

theorem r_hd : penumHdK (pidn 42 6) HRE.cnt 64 HRE.T HRE.PL = true := by
  quickRfl

theorem r_sl : penumSlK 42 6 (mask 6) (42 * 6) false HRE.G HRE.GI HRE.k HRE.cnt HRE.T HRE.PL
    HRE.POS HRE.SRT HRE.SRI 0 64 = true := by
  quickRfl

theorem r_norm : allN 9 (fun j => allN 6 (fun i =>
    bAnd(strictB (HNP1 (Nat.add (Nat.mul 6 j) i)) (fun q => bAnd(Nat.blt q HRE.cnt,
      Nat.beq (HRE.T q) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (HXE.G j) (HRE.G i)) (HXI j)))),
    strictB (HNP2 (Nat.add (Nat.mul 6 j) i)) (fun q => bAnd(Nat.blt q HRE.cnt,
      Nat.beq (HRE.T q) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (HXI j) (HRE.G i)) (HXE.G j))))))) =
    true := by
  quickRfl

theorem x_comm : Nat.beq (cntK (fun t => allN 6 (fun g => Nat.beq (pcomp 42 6 (mask 6) (HXE.T t)
    (HRE.G g)) (pcomp 42 6 (mask 6) (HRE.G g) (HXE.T t)))) 168) 64 = true := by
  quickRfl

end CertificateChecks.KernelSpor.He2276

end
