module

public import Certificates.Kernel.LocalQT.He4148.Glue
public import Certificates.Kernel.SporSch.Mathieu.GenNL
public import CFSG.Certificates.Kernel.SporSch.NoLayerSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerCheckInputs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerData
public meta import CFSG.Sporadic.HeldB.InnerData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathData
public import CFSG.Sporadic.HeldB.ClassCount
public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M23CheckBase
public import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLQT.He4148

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.HeldB

meta def SX1 : Array (Array Nat) := strongOf 42 heInnerSigma1.toArray heInnerChainWords1

meta def baseX1 : Array Nat := #[0, 1, 7, 10, 3, 2]

end CertificateChecks.KernelLQT.He4148

#ks_rawchain CertificateChecks.KernelLQT.He4148.X1Q 42 6 16 CertificateChecks.KernelLQT.He4148.SX1
  CertificateChecks.KernelLQT.He4148.baseX1 9 CFSG.Sporadic.HeldB.heInnerChainWords1

#kss_packs CertificateChecks.KernelLQT.He4148.E1 6 CFSG.QuasithinUnique.Id2519.HeInner.he1E

#kss_nlk CertificateChecks.KernelLQT.He4148.K1 CertificateChecks.KernelLQT.He4148.X1Q 42 6 6
  CertificateChecks.KernelLQT.He4148.E1 1024 11

namespace CertificateChecks.KernelLQT.He4148

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Sporadic.HeldB CFSG.QuasithinUnique.Id2519.MathNoLayer
open CFSG.QuasithinUnique.Id2519.HeInner CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

theorem bX1 : bindsK 42 6 X1Q.S X1Q.SI heInnerSigma1 0 = true := by quickRfl

theorem b1 : bindLs 42 6 he1E E1 = true := by quickRfl

theorem i1 : memL (pidn 42 6) E1 = true := by quickRfl

theorem e1 : nlE 42 6 (mask 6) (42 * 6) (pidn 42 6) X1Q.LR X1Q.TRI X1Q.BP 6 X1Q.S X1Q.SI 9 E1
    E1 = true := by quickRfl

theorem n1 : Nat.ble (ordK X1Q.LR 6) (11 * 1024) = true := by quickRfl

theorem len_X1 : heInnerSigma1.length = 9 := rfl

theorem chainX1 : ChainK 42 6 (heInnerSigma1.map (permOrId 42)) heInnerChainWords1
    (#v[0, 1, 7, 10, 3, 2] : Vector (Fin 42) 6) X1Q.S X1Q.SI X1Q.LR X1Q.TR X1Q.TRI 17 X1Q.BP 3
    16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, X1Q.head, X1Q.hl,
    by norm_num, X1Q.hs⟩
  have hj' : j < heInnerSigma1.length := by simpa using hj
  rw [getD_map_lt _ #[] _ hj']
  have h := bindsK_spec bX1 j hj'
  rw [Nat.zero_add] at h
  exact imageList_bind h

theorem he1_noLayer : noLayerOK 42 (heToTabs he1E) (allTables heX1) = true :=
  chainK_noLayer (by decide) (by decide) chainX1 b1 i1 e1 (Nat.le_of_ble_eq_true n1) K1.hK

end CertificateChecks.KernelLQT.He4148

end
