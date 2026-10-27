module

public import Certificates.Kernel.UnitarySix.Sec3.E3600Chk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

theorem kGP : ∀ k < 18, PermK (sec3G k) (pinvS 693 10 (mask 10) (sec3G k)) = true := by
  decide +kernel

theorem chK1_P : ∀ j < chK1.gens.length, PermK (CK1.S j) (CK1.SI j) = true := by decide +kernel
theorem chK2_P : ∀ j < chK2.gens.length, PermK (CK2.S j) (CK2.SI j) = true := by decide +kernel
theorem chA1_P : ∀ j < chA1.gens.length, PermK (CA1.S j) (CA1.SI j) = true := by decide +kernel
theorem chA2_P : ∀ j < chA2.gens.length, PermK (CA2.S j) (CA2.SI j) = true := by decide +kernel
theorem chK1A1_P : ∀ j < chK1A1.gens.length, PermK (CK1A1.S j) (CK1A1.SI j) = true := by
  decide +kernel
theorem chT2_P : ∀ j < chT2.gens.length, PermK (CT2.S j) (CT2.SI j) = true := by decide +kernel

@[expose] noncomputable def sfA1 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CA1.LR CA1.TRI CA1.BP 1 0 G
@[expose] noncomputable def sfA2 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CA2.LR CA2.TRI CA2.BP 3 0 G

theorem kU : ((List.range chK1.gens.length).all fun j =>
      sfK1 (pcomp 693 10 (mask 10) (wK wu₁) (pcomp 693 10 (mask 10) (CK1.S j) (wKI wu₁)))) &&
    ((List.range chK2.gens.length).all fun j =>
      sfK2 (pcomp 693 10 (mask 10) (wK wu₂) (pcomp 693 10 (mask 10) (CK2.S j) (wKI wu₂)))) =
      true := by
  decide +kernel

theorem kKN : ((List.range chK1.gens.length).all fun j => (List.range chA1.gens.length).all fun i =>
      sfA1 (pcomp 693 10 (mask 10) (CK1.S j) (pcomp 693 10 (mask 10) (CA1.S i) (CK1.SI j)))) &&
    ((List.range chK2.gens.length).all fun j => (List.range chA2.gens.length).all fun i =>
      sfA2 (pcomp 693 10 (mask 10) (CK2.S j) (pcomp 693 10 (mask 10) (CA2.S i) (CK2.SI j)))) =
      true := by
  decide +kernel

theorem kSN : ((List.range chS.gens.length).all fun j =>
      sfS (pcomp 693 10 (mask 10) (wK wj₀) (pcomp 693 10 (mask 10) (CS.S j) (wKI wj₀)))) &&
    ((List.range 15).all fun k => sfS (sec3G k)) = true := by
  decide +kernel

theorem kFix : ((List.range chS.gens.length).all fun j => pg 10 (mask 10) (CS.S j) 0 == 0) &&
    allN 693 (fun p => p == 0 || (List.range chS.gens.length).any fun j =>
      pg 10 (mask 10) (CS.S j) p != p) &&
    ((List.range chK1A1.gens.length).all fun j => pg 10 (mask 10) (CK1A1.S j) 0 == 0) = true := by
  decide +kernel

theorem kSF : (pg 10 (mask 10) (wK wu₂) 381 == 0 && pg 10 (mask 10) (wK wu₁) 1 == 0 &&
    pg 10 (mask 10) (wK ww₀) 1 == 0 &&
    ((List.range chT2.gens.length).all fun j => pg 10 (mask 10) (CT2.S j) 381 == 381) &&
    (List.range chT1.gens.length).all fun j => pg 10 (mask 10) (CT1.S j) 1 == 1) = true := by
  decide +kernel

theorem kLab : ((List.range chT1.gens.length).all fun j => allN 693 fun p =>
    pg 10 (mask 10) sec3LabT1 (pg 10 (mask 10) (CT1.S j) p) == pg 10 (mask 10) sec3LabT1 p) =
      true := by
  decide +kernel

theorem kT1K1 : ((List.range chT1.gens.length).all fun j => sfK1 (CT1.S j)) = true := by
  decide +kernel

end CertificateChecks.KernelU6.Sec3
