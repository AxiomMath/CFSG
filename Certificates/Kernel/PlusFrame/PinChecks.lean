module

public import Certificates.Kernel.PlusFrame.Pins
public import Certificates.Kernel.PlusFactors.Checks
public import Certificates.Data.Kernel.PlusFrameK

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPlusFr

open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.PlusFrame CFSG.KC.Enum
  CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit
open CFSG.KLie.CT (anyN)
open CertificateChecks.KernelPlusF

@[expose] def frV (i : Nat) : Nat :=
  cond (Nat.beq i 0) 18 (cond (Nat.beq i 1) 31 (cond (Nat.beq i 2) 36 41))

@[expose] noncomputable def mapsP (x : Nat) : Bool :=
  allN 4 fun i => anyN 4 fun j => Nat.beq (pg 6 (mask 6) x (frV i)) (frV j)

@[expose] noncomputable def matchP (x : Nat) (σ : Fin 4 → Fin 4) : Bool :=
  allN 4 fun i => Nat.beq (pg 6 (mask 6) x (frV i)) (frV (σ (Fin.ofNat 4 i)).val)

@[expose] noncomputable def evenP (x : Nat) : Bool :=
  !(mapsP x) || oddPerms.all fun σ => !(matchP x σ)

theorem kNumsF : (Nat.beq PT.ng 3 && Nat.beq PT.N 32 && Nat.beq PC0.ng 3 && Nat.beq PC0.N 8 &&
    Nat.beq PC1.ng 3 && Nat.beq PC1.N 8 && Nat.beq PC2.ng 3 && Nat.beq PC2.N 8 &&
    Nat.beq PC3.ng 3 && Nat.beq PC3.N 8) = true := by decide +kernel

theorem kBindT : (Nat.beq t0Gens.size 3 &&
    allN 3 fun k => bindArrK t0Gens[k]! 60 6 (PT.G k)) = true := by decide +kernel
theorem kBindC0 : (Nat.beq (otherRows 0).size 3 &&
    allN 3 fun k => bindArrK (otherRows 0)[k]! 60 6 (PC0.G k)) = true := by decide +kernel
theorem kBindC1 : (Nat.beq (otherRows 1).size 3 &&
    allN 3 fun k => bindArrK (otherRows 1)[k]! 60 6 (PC1.G k)) = true := by decide +kernel
theorem kBindC2 : (Nat.beq (otherRows 2).size 3 &&
    allN 3 fun k => bindArrK (otherRows 2)[k]! 60 6 (PC2.G k)) = true := by decide +kernel
theorem kBindC3 : (Nat.beq (otherRows 3).size 3 &&
    allN 3 fun k => bindArrK (otherRows 3)[k]! 60 6 (PC3.G k)) = true := by decide +kernel

theorem kPermF : (allN 3 (gOK PT.G) && allN 3 (gOK PC0.G) && allN 3 (gOK PC1.G) &&
    allN 3 (gOK PC2.G) && allN 3 (gOK PC3.G)) = true := by decide +kernel

theorem kKT : keysSK 60 6 plusBase PT.N PT.T ((List.range 32).map KT) = true := by decide +kernel
theorem kKC0 : keysSK 60 6 plusBase PC0.N PC0.T ((List.range 8).map KC0) = true := by
  decide +kernel
theorem kKC1 : keysSK 60 6 plusBase PC1.N PC1.T ((List.range 8).map KC1) = true := by
  decide +kernel
theorem kKC2 : keysSK 60 6 plusBase PC2.N PC2.T ((List.range 8).map KC2) = true := by
  decide +kernel
theorem kKC3 : keysSK 60 6 plusBase PC3.N PC3.T ((List.range 8).map KC3) = true := by
  decide +kernel

theorem kSub : allN 3 (fun k => memT PE.N PE.T (PT.G k)) = true := by decide +kernel

theorem kMemF : allN 60 (fun k => memT PT.N PT.T (PE.G k) == CFSG.KC.PlusFrameK.isFr k) = true := by
  decide +kernel

theorem kEven : allN PE.N (fun k => evenP (PE.T k)) = true := by decide +kernel

theorem kAlt : evenPerms.all (fun σ => anyN PE.N fun k => matchP (PE.T k) σ) = true := by
  decide +kernel

end CertificateChecks.KernelPlusFr
