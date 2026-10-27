module

public import Certificates.Kernel.LocalComp.E8Tables
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.WeylE8.Refl
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import Certificates.Kernel.LocalComp.WeylBase
public meta import Certificates.Kernel.LocalComp.WeylBase
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelLC.W3184.W 240 8 16 CFSG.EvenSmallLie.OmegaEight.Weyl.wS
  CertificateChecks.KernelLC.Weyl.wBaseArr 13 CertificateChecks.KernelLC.Weyl.nilD

namespace CertificateChecks.KernelLC.W3184

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight.Weyl

@[expose] noncomputable def SG : Nat := nat_lit 8584010032186255552320307593728

@[expose] noncomputable def POS : Nat := nat_lit 9095475952674774304507807957321840237464309005709120158787688451663750799642112187528556741988751425620107185335232524594572522132686620450323820634086935807914865480768114404553339753980768657906473410622970127698330042301591339385361965547122788674058942197873551440674460222696890564864

@[expose] noncomputable def WIT : Nat := nat_lit 20948055459829362769773137309750634052281077288760362111416369885362431493702619068451131623111610217744838362974668740626713839987603990188265675609879332095443979015394260063658006145802914181610301707634334847563939180186962339542738788444038758973036541854264713836177903823660408071392105119043622186099555742799719912626055265076917333916581537173188960335226812796441630204482687498393625165961863948001492980552688387703890753154284113092069504018543516910327232919259376480330315906003254202430910871753607723027214839491122367042409099877734280904206636937476527161600

@[expose] noncomputable def posT (j : Nat) : Nat := E8.RT (pg 8 255 POS j)

theorem kSG : bindList sgsRoots 13 SG = true := by quickRfl

theorem kSGS : allN 13 (fun j => Nat.beq (W.S j) (E8.RT (pg 8 255 SG j))) = true := by quickRfl

theorem kPOS : bindList posRoots 120 POS = true := by quickRfl

theorem kRefl : reflFacts E8.RT E8.NEG WIT posT = true := by quickRfl

theorem kNeg : negFacts E8.RT E8.NEG = true := by quickRfl

theorem kSift : allN 240 (fun r => bAnd(Nat.beq (Nat.shiftRight (E8.RT r) 1920) 0,
    siftK 240 8 (mask 8) (240 * 8) (pidn 240 8) W.LR W.TRI W.BP 8 0 (E8.RT r))) = true := by
  quickRfl

theorem perm : allN 13 (fun j => permOK 240 8 (mask 8) (240 * 8) (W.S j) (W.SI j)) = true := by
  quickRfl

end CertificateChecks.KernelLC.W3184

end
