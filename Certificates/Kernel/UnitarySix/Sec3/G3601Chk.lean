module

public import Certificates.Kernel.UnitarySix.Sec3.G3600Chk
public import Certificates.Kernel.UnitarySix.Sec3.CA3
public import Certificates.Kernel.UnitarySix.Sec3.CA4
public import Certificates.Kernel.UnitarySix.Sec3.CX8
public import Certificates.Kernel.UnitarySix.Sec3.CSig
public import Certificates.Kernel.UnitarySix.Sec3.CLam
public import Certificates.Kernel.UnitarySix.Sec3.CZ2S
public import Certificates.Kernel.UnitarySix.Sec3.CX6Z
public import Certificates.Kernel.UnitarySix.Sec3.CZ
public import Certificates.Kernel.UnitarySix.Sec3.CX1Z
public import Certificates.Kernel.UnitarySix.Sec3.CP2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

theorem kXId : (xIds.all fun p => Nat.beq (wK p.1) (wK p.2)) = true := by decide +kernel

theorem kXComm : ((chA2.gens.all fun a => chA2.gens.all fun b =>
      Nat.beq (wK (a ++ b)) (wK (b ++ a))) &&
    (chA3.gens.all fun a => chA4.gens.all fun b => Nat.beq (wK (a ++ b)) (wK (b ++ a))) &&
    ([[4, 17]].all fun a => chA4.gens.all fun b => Nat.beq (wK (a ++ b)) (wK (b ++ a))) &&
    (chSig.gens.all fun a => chA4.gens.all fun b => Nat.beq (wK (a ++ b)) (wK (b ++ a))) &&
    (chLam.gens.all fun a => chSig.gens.all fun b => Nat.beq (wK (a ++ b)) (wK (b ++ a))) &&
    (chK1.gens.all fun a => [[14]].all fun b => Nat.beq (wK (a ++ b)) (wK (b ++ a))) &&
    (chS.gens.all fun a => [[14]].all fun b => Nat.beq (wK (a ++ b)) (wK (b ++ a))) &&
    (chA1.gens.all fun a => [[14]].all fun b => Nat.beq (wK (a ++ b)) (wK (b ++ a)))) = true := by
  decide +kernel

theorem kXWit : ((a4cData.all fun p => Nat.beq (wK [p.1]) (wK (prodWord cwW p.2))) &&
    (a4aData.all fun p => Nat.beq (wK [p.1]) (wK (prodWord cjW p.2))) &&
    (a4zData.all fun p => Nat.beq (wK [p.1]) (wK (prodWord cjW p.2))) &&
    (a4jData.all fun p => Nat.beq (wK [p.1]) (wK (prodWord cwW p.2))) &&
    (k1pData.all fun p => Nat.beq (wK [p.1]) (wK (prodWord cwW p.2))) &&
    (a1cData.all fun p => Nat.beq (wK [p.1]) (wK (prodWord cjW p.2))) &&
    (a2cData.all fun p => Nat.beq (wK [p.1]) (wK (prodWord cjW p.2))) &&
    (a12cData.all fun p => Nat.beq (wK [p.1]) (wK (prodWord cwW p.2))) &&
    (a3eData.all fun p => Nat.beq (wK [p.1]) (wK (cwW p.2.1 [4, 17] ++ p.2.2)))) = true := by
  decide +kernel

@[expose] noncomputable def sfA3 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CA3.LR CA3.TRI CA3.BP 2 0 G
@[expose] noncomputable def sfA4 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CA4.LR CA4.TRI CA4.BP 2 0 G

theorem chLam_P : ∀ j < chLam.gens.length, PermK (CLam.S j) (CLam.SI j) = true := by
  decide +kernel
theorem chSig_P : ∀ j < chSig.gens.length, PermK (CSig.S j) (CSig.SI j) = true := by
  decide +kernel
theorem chA3_P : ∀ j < chA3.gens.length, PermK (CA3.S j) (CA3.SI j) = true := by decide +kernel
theorem chA4_P : ∀ j < chA4.gens.length, PermK (CA4.S j) (CA4.SI j) = true := by decide +kernel

theorem perm_words2 : ∀ w ∈ [[4, 17], [15, 1, 15, 0, 1, 15, 1, 15, 1, 15, 0, 1, 15, 1],
    [16, 17, 16]], PermK (wK w) (wKI w) = true := by
  decide +kernel

theorem kXN : ((List.range chLam.gens.length).all fun j => (List.range chA4.gens.length).all
      fun i => sfA4 (pcomp 693 10 (mask 10) (CLam.S j) (pcomp 693 10 (mask 10) (CA4.S i) (CLam.SI j)))) &&
    ((List.range chLam.gens.length).all fun j => (List.range chA3.gens.length).all fun i =>
      sfA3 (pcomp 693 10 (mask 10) (CLam.S j) (pcomp 693 10 (mask 10) (CA3.S i) (CLam.SI j)))) &&
    ((List.range chSig.gens.length).all fun j => (List.range chA3.gens.length).all fun i =>
      sfA3 (pcomp 693 10 (mask 10) (CSig.S j) (pcomp 693 10 (mask 10) (CA3.S i) (CSig.SI j)))) &&
    ((List.range chA3.gens.length).all fun i =>
      sfA3 (pcomp 693 10 (mask 10) (wK [4, 17]) (pcomp 693 10 (mask 10) (CA3.S i) (wKI [4, 17])))) &&
    ((List.range chA3.gens.length).all fun i =>
      sfA3 (pcomp 693 10 (mask 10) (wK wj₀) (pcomp 693 10 (mask 10) (CA3.S i) (wKI wj₀)))) =
      true := by
  decide +kernel

theorem kXF : (allN 693 (fun p => fixF.contains p ==
      (List.range chA3.gens.length).all fun j => pg 10 (mask 10) (CA3.S j) p == p) &&
    (List.range 5).all fun i => pg 10 (mask 10) (wK qF[i]!) fixF[i]! == 0) = true := by
  decide +kernel

end CertificateChecks.KernelU6.Sec3
