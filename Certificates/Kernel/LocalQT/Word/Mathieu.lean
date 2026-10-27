
module

public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverSporadicInputs
import Certificates.Kernel.LocalQT.Cmd
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

set_option maxRecDepth 100000

#lqt_chars CFSG.KD.LQT.M12X CFSG.SectionRank.m12WordX
#lqt_chars CFSG.KD.LQT.M12Y CFSG.SectionRank.m12WordY
#lqt_chars CFSG.KD.LQT.M12H CFSG.SectionRank.m12WordH
#lqt_chars CFSG.KD.LQT.M24X CFSG.SectionRank.m24WordX
#lqt_chars CFSG.KD.LQT.M24Y CFSG.SectionRank.m24WordY
#lqt_chars CFSG.KD.LQT.M24H CFSG.SectionRank.m24WordH
#lqt_chars CFSG.KD.LQT.M11X CFSG.QuasithinUnique.Ch1.m11WordX
#lqt_chars CFSG.KD.LQT.M11Y CFSG.QuasithinUnique.Ch1.m11WordY
#lqt_chars CFSG.KD.LQT.M11H CFSG.QuasithinUnique.Ch1.m11WordH
#lqt_chars CFSG.KD.LQT.M23X CFSG.QuasithinUnique.Ch1.m23WordX
#lqt_chars CFSG.KD.LQT.M23Y CFSG.QuasithinUnique.Ch1.m23WordY
#lqt_chars CFSG.KD.LQT.M23H CFSG.QuasithinUnique.Ch1.m23WordH

public section

namespace CertificateChecks.KernelLocalQT

open Equiv CFSG.SectionRank CFSG.QuasithinUnique.Ch1 CFSG.KC.LQT CFSG.KD.LQT
open scoped commutatorElement

theorem m12A_img : ∀ i : Fin 12, ((m12LocA : Perm (Fin 12)) i : ℕ) = P.img 184726996899603491 i := by
  decide +kernel
theorem m12B_img : ∀ i : Fin 12, ((m12LocB : Perm (Fin 12)) i : ℕ) = P.img 365002956609719367 i := by
  decide +kernel
theorem m24A_img : ∀ i : Fin 24,
    ((m24LocA : Perm (Fin 24)) i : ℕ) = P.img 817395973838868159142633316802379971 i := by
  decide +kernel
theorem m24B_img : ∀ i : Fin 24,
    ((m24LocB : Perm (Fin 24)) i : ℕ) = P.img 938078705133617800621527216201835139 i := by
  decide +kernel
theorem m11A_img : ∀ i : Fin 11, ((m11LocA : Perm (Fin 11)) i : ℕ) = P.img 3420860021279008 i := by
  decide +kernel
theorem m11B_img : ∀ i : Fin 11, ((m11LocB : Perm (Fin 11)) i : ℕ) = P.img 11576764645055619 i := by
  decide +kernel
theorem m23A_img : ∀ i : Fin 23,
    ((m23LocA : Perm (Fin 23)) i : ℕ) = P.img 29396287020561317414859794500619265 i := by
  decide +kernel
theorem m23B_img : ∀ i : Fin 23,
    ((m23LocB : Perm (Fin 23)) i : ℕ) = P.img 4436007312844787929641103698034959 i := by
  decide +kernel

theorem m12_ok : W.cub3OK 12 184726996899603491 365002956609719367 M12X M12Y M12H 2 0 1 0 2 1 1 =
    true := by quickRfl
theorem m24_ok : W.cub3OK 24 817395973838868159142633316802379971
    938078705133617800621527216201835139 M24X M24Y M24H 0 1 0 2 0 0 1 = true := by quickRfl
theorem m11_ok : W.sq3OK 11 3420860021279008 11576764645055619 M11X M11Y M11H 2 0 2 1 = true := by
  quickRfl
theorem m23_ok : W.sq3OK 23 29396287020561317414859794500619265
    4436007312844787929641103698034959 M23X M23Y M23H 1 2 0 2 = true := by quickRfl

theorem mathieu_local :
    (let x := mathieuWord m12LocA m12LocB m12WordX.toList
      let y := mathieuWord m12LocA m12LocB m12WordY.toList
      let h := mathieuWord m12LocA m12LocB m12WordH.toList
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
        (Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
          x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ)) ∧
        h * x * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 1 ∧
        h * y * h⁻¹ = x ^ 0 * y ^ 2 * ⁅x, y⁆ ^ 1 ∧
        h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1)
    ∧ (let x := mathieuWord m24LocA m24LocB m24WordX.toList
      let y := mathieuWord m24LocA m24LocB m24WordY.toList
      let h := mathieuWord m24LocA m24LocB m24WordH.toList
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
        (Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
          x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ)) ∧
        h * x * h⁻¹ = x ^ 0 * y ^ 1 * ⁅x, y⁆ ^ 0 ∧
        h * y * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
        h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1) := by
  rw [M12X_toList, M12Y_toList, M12H_toList, M24X_toList, M24Y_toList, M24H_toList]
  exact ⟨W.cub3_sound m12LocA m12LocB m12A_img m12B_img m12_ok,
    W.cub3_sound m24LocA m24LocB m24A_img m24B_img m24_ok⟩

theorem three_cover :
    (mathieuWord m11LocA m11LocB m11WordX.toList ^ 3 = 1)
    ∧ (mathieuWord m11LocA m11LocB m11WordY.toList ^ 3 = 1)
    ∧ (mathieuWord m11LocA m11LocB m11WordX.toList * mathieuWord m11LocA m11LocB m11WordY.toList =
            mathieuWord m11LocA m11LocB m11WordY.toList *
              mathieuWord m11LocA m11LocB m11WordX.toList)
    ∧ (Function.Injective fun t : Fin 3 × Fin 3 =>
            mathieuWord m11LocA m11LocB m11WordX.toList ^ (t.1 : ℕ) *
              mathieuWord m11LocA m11LocB m11WordY.toList ^ (t.2 : ℕ))
    ∧ (mathieuWord m11LocA m11LocB m11WordH.toList * mathieuWord m11LocA m11LocB m11WordX.toList *
              (mathieuWord m11LocA m11LocB m11WordH.toList)⁻¹ =
            mathieuWord m11LocA m11LocB m11WordX.toList ^ 2 *
              mathieuWord m11LocA m11LocB m11WordY.toList ^ 0)
    ∧ (mathieuWord m11LocA m11LocB m11WordH.toList * mathieuWord m11LocA m11LocB m11WordY.toList *
              (mathieuWord m11LocA m11LocB m11WordH.toList)⁻¹ =
            mathieuWord m11LocA m11LocB m11WordX.toList ^ 2 *
              mathieuWord m11LocA m11LocB m11WordY.toList ^ 1)
    ∧ (mathieuWord m23LocA m23LocB m23WordX.toList ^ 3 = 1)
    ∧ (mathieuWord m23LocA m23LocB m23WordY.toList ^ 3 = 1)
    ∧ (mathieuWord m23LocA m23LocB m23WordX.toList * mathieuWord m23LocA m23LocB m23WordY.toList =
            mathieuWord m23LocA m23LocB m23WordY.toList *
              mathieuWord m23LocA m23LocB m23WordX.toList)
    ∧ (Function.Injective fun t : Fin 3 × Fin 3 =>
            mathieuWord m23LocA m23LocB m23WordX.toList ^ (t.1 : ℕ) *
              mathieuWord m23LocA m23LocB m23WordY.toList ^ (t.2 : ℕ))
    ∧ (mathieuWord m23LocA m23LocB m23WordH.toList * mathieuWord m23LocA m23LocB m23WordX.toList *
              (mathieuWord m23LocA m23LocB m23WordH.toList)⁻¹ =
            mathieuWord m23LocA m23LocB m23WordX.toList ^ 1 *
              mathieuWord m23LocA m23LocB m23WordY.toList ^ 2)
    ∧ (mathieuWord m23LocA m23LocB m23WordH.toList * mathieuWord m23LocA m23LocB m23WordY.toList *
              (mathieuWord m23LocA m23LocB m23WordH.toList)⁻¹ =
            mathieuWord m23LocA m23LocB m23WordX.toList ^ 0 *
              mathieuWord m23LocA m23LocB m23WordY.toList ^ 2) := by
  rw [M11X_toList, M11Y_toList, M11H_toList, M23X_toList, M23Y_toList, M23H_toList]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := W.sq3_sound m11LocA m11LocB m11A_img m11B_img m11_ok
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := W.sq3_sound m23LocA m23LocB m23A_img m23B_img m23_ok
  exact ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6⟩

end CertificateChecks.KernelLocalQT

end
