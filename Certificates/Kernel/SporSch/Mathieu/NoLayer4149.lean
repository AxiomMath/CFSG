module

public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import Certificates.Kernel.SporSch.Mathieu.M22OFacts
public import Certificates.Kernel.SporSch.Mathieu.M24Facts
public import Certificates.Kernel.SporSch.Mathieu.GenNL
public import CFSG.Certificates.Kernel.SporSch.NoLayerSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_packs CertificateChecks.KernelSporSch.NoLayer.E23 5
  CFSG.QuasithinUnique.Id2519.MathNoLayer.m23E

#kss_packs CertificateChecks.KernelSporSch.NoLayer.E22 5
  CFSG.QuasithinUnique.Id2519.MathNoLayer.m22oE

#kss_packs CertificateChecks.KernelSporSch.NoLayer.E24 5
  CFSG.QuasithinUnique.Id2519.MathNoLayer.m24E

#kss_nlk CertificateChecks.KernelSporSch.NoLayer.K23 CertificateChecks.KernelSporSch.M23C1 23 5 4
  CertificateChecks.KernelSporSch.NoLayer.E23 1024 3

#kss_nlk CertificateChecks.KernelSporSch.NoLayer.K22 CertificateChecks.KernelSporSch.M22OC2 22 5 3
  CertificateChecks.KernelSporSch.NoLayer.E22 1024 2

#kss_nlk CertificateChecks.KernelSporSch.NoLayer.K24 CertificateChecks.KernelSporSch.M24C2 24 5 4
  CertificateChecks.KernelSporSch.NoLayer.E24 1024 21

namespace CertificateChecks.KernelSporSch.NoLayer

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC
open CFSG.QuasithinUnique.Id2519.MathNoLayer
open CertificateChecks.KernelSporSch

theorem b23 : bindLs 23 5 m23E E23 = true := by quickRfl
theorem i23 : memL (pidn 23 5) E23 = true := by quickRfl
theorem e23 : nlE 23 5 (mask 5) (23 * 5) (pidn 23 5) M23C1.LR M23C1.TRI M23C1.BP 4 M23C1.S
    M23C1.SI 4 E23 E23 = true := by quickRfl
theorem n23 : Nat.ble (ordK M23C1.LR 4) (3 * 1024) = true := by quickRfl

theorem b22 : bindLs 22 5 m22oE E22 = true := by quickRfl
theorem i22 : memL (pidn 22 5) E22 = true := by quickRfl
theorem e22 : nlE 22 5 (mask 5) (22 * 5) (pidn 22 5) M22OC2.LR M22OC2.TRI M22OC2.BP 3 M22OC2.S
    M22OC2.SI 3 E22 E22 = true := by quickRfl
theorem n22 : Nat.ble (ordK M22OC2.LR 3) (2 * 1024) = true := by quickRfl

theorem b24 : bindLs 24 5 m24E E24 = true := by quickRfl
theorem i24 : memL (pidn 24 5) E24 = true := by quickRfl
theorem e24 : nlE 24 5 (mask 5) (24 * 5) (pidn 24 5) M24C2.LR M24C2.TRI M24C2.BP 4 M24C2.S
    M24C2.SI 2 E24 E24 = true := by quickRfl
theorem n24 : Nat.ble (ordK M24C2.LR 4) (21 * 1024) = true := by quickRfl

theorem facts : (noLayerOK 23 (toTabs m23E) (allTables m23CentQ1) = true)
    ∧ (noLayerOK 22 (toTabs m22oE) (allTables m22OutCentQ2) = true)
    ∧ (noLayerOK 24 (toTabs m24E) (allTables m24CentQ2) = true) :=
  ⟨chainK_noLayer (by decide) (by decide) M23OC.chainC1 b23 i23 e23 (Nat.le_of_ble_eq_true n23)
      K23.hK,
    chainK_noLayer (by decide) (by decide) M22OC.chainO2 b22 i22 e22 (Nat.le_of_ble_eq_true n22)
      K22.hK,
    chainK_noLayer (by decide) (by decide) M24OC.chainC2 b24 i24 e24 (Nat.le_of_ble_eq_true n24)
      K24.hK⟩

end CertificateChecks.KernelSporSch.NoLayer

end
