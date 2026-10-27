module

public import Certificates.Kernel.SporSch.Mathieu.M23Data
public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMathieuData
public meta import Certificates.Kernel.SporSch.Mathieu.M23Data
public meta import Certificates.Kernel.SporSch.Mathieu.M22Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMathieuData
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M23

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.C4121

open CFSG.KS.SporSch.MOCG CFSG.QuasithinUnique.DoubleA3.K32Mathieu

meta def SC23 : Array (Array Nat) :=
  strongOf 23 (m23Cent3Words.map (evalW 23 #[CertificateChecks.KernelSporSch.M23OC.tAM,
    CertificateChecks.KernelSporSch.M23OC.tBM])).toArray m23Cent3ChainWords

meta def base23 : Array Nat := #[0, 2]

meta def rep23 : Array (Array Nat) :=
  (m23Rep3Words.map (evalW 23 #[CertificateChecks.KernelSporSch.M23OC.tAM,
    CertificateChecks.KernelSporSch.M23OC.tBM])).toArray

meta def SC22 : Array (Array Nat) :=
  strongOf 22 (m22Cent3Words.map (evalW 22 #[CertificateChecks.KernelSporSch.M22OC.tAM,
    CertificateChecks.KernelSporSch.M22OC.tBM])).toArray m22Cent3ChainWords

meta def base22 : Array Nat := #[0, 1]

meta def rep22 : Array (Array Nat) :=
  (m22Rep3Words.map (evalW 22 #[CertificateChecks.KernelSporSch.M22OC.tAM,
    CertificateChecks.KernelSporSch.M22OC.tBM])).toArray

end CFSG.KD.LQT.C4121

#ks_rawchain CFSG.KD.LQT.M23C3 23 5 16 CFSG.KD.LQT.C4121.SC23 CFSG.KD.LQT.C4121.base23 3
  CFSG.QuasithinUnique.DoubleA3.K32Mathieu.m23Cent3ChainWords

#ks_rawchain CFSG.KD.LQT.M22C3 22 5 16 CFSG.KD.LQT.C4121.SC22 CFSG.KD.LQT.C4121.base22 4
  CFSG.QuasithinUnique.DoubleA3.K32Mathieu.m22Cent3ChainWords

end
