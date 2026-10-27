module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCases
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCases
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Va

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.PSL3Four.Native

meta def inM : Array (Array Nat) := #[rep8, vaZ] ++ vaCg ++ #[phiArr, deltaArr]

meta def inIM : Array (Array Nat) := inM.map (CFSG.Monster.B.Co2.Native.invCand 820)

meta def cosM : Array (Array Nat) := inM.mapIdx fun i x =>
  if 1 ≤ i ∧ i ≤ 6 then
    #[([0, 2, 4, 6].find? fun k =>
      inP (CFSG.Monster.B.Co2.Native.compA 820 x (CFSG.Monster.B.Co2.Native.invCand 820 (tArr k))))
      |>.getD 0]
  else #[0]

meta def idM : Array Nat := idTab 820

meta def gM : Array (Array Nat) := vaCg

meta def gIM : Array (Array Nat) := gM.map (CFSG.Monster.B.Co2.Native.invCand 820)

meta def ids5M : Array (Array Nat) := Array.replicate 5 idM

meta def recM : Array (Array Nat) := (bfs (fun j t => conjTab 820 idM gM[j]! t) 5 idM 50000).tabs

meta def clM : Array (Array Nat) :=
  (recM.map fun x => (gM ++ gIM).map fun g => comp 820 x g).flatten

end CertificateChecks.KernelHSStd.U43Va

#kmisc_packarrs CertificateChecks.KernelHSStd.U43VP CertificateChecks.KernelHSStd.U43Va.inM 10
#kmisc_packarrs CertificateChecks.KernelHSStd.U43VI CertificateChecks.KernelHSStd.U43Va.inIM 10
#kmisc_packarrs CertificateChecks.KernelHSStd.U43VC CertificateChecks.KernelHSStd.U43Va.cosM 8
#kmulh CertificateChecks.KernelHSStd.U43VA 820 10 CertificateChecks.KernelHSStd.U43Va.ids5M
  CertificateChecks.KernelHSStd.U43Va.gM CertificateChecks.KernelHSStd.U43Va.idM 50000
#kfind CertificateChecks.KernelHSStd.U43VACl CertificateChecks.KernelHSStd.U43Va.recM
  CertificateChecks.KernelHSStd.U43Va.clM

end
