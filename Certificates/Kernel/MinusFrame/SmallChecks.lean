module

public import Certificates.Kernel.MinusFrame.Small
public import Certificates.Kernel.MinusEnum.Data
public import Certificates.Kernel.MinusFrame.Data
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.PermPinK
public import Certificates.Data.Kernel.Misc.PermWit
public import CFSG.Certificates.Kernel.LocalCompUnpack

public section

namespace CertificateChecks.KernelMinusFrame

open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.MinusFrame
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.KC.PermPinK

@[expose] noncomputable def gOK (G : ℕ → ℕ) (k : ℕ) : Bool :=
  permOK 65 7 (mask 7) (Nat.mul 65 7) (G k) (pinvS 65 7 (mask 7) (G k))

@[expose] noncomputable def sk0 : List ℕ := (List.range 16).map K0
@[expose] noncomputable def skL : List ℕ := (List.range 120).map KL
@[expose] noncomputable def skA : List ℕ := (List.range 60).map KA

theorem kNumsS : (Nat.beq S0.ng 3 && Nat.beq S0.N 16 && Nat.beq SL.ng 15 && Nat.beq SL.N 120 &&
    Nat.beq SA.ng 2 && Nat.beq SA.N 60) = true := by decide +kernel

theorem kBind0 : (Nat.beq t0Gens.size 3 &&
    allN 3 fun k => bindArrK t0Gens[k]! 65 7 (S0.G k)) = true := by decide +kernel

theorem kBindL : (Nat.beq l0Gens.size 15 &&
    allN 15 fun k => bindArrK l0Gens[k]! 65 7 (SL.G k)) = true := by decide +kernel

theorem kBindA : (Nat.beq aGens.size 2 &&
    allN 2 fun k => bindArrK aGens[k]! 65 7 (SA.G k)) = true := by decide +kernel

theorem kPermS : (allN 3 (gOK S0.G) && allN 15 (gOK SL.G) && allN 2 (gOK SA.G)) = true := by
  decide +kernel

theorem kPermTA : allN 60 (gOK SA.T) = true := by decide +kernel

theorem kK0 : keysSK 65 7 minusBase S0.N S0.T sk0 = true := by decide +kernel
theorem kKL : keysSK 65 7 minusBase SL.N SL.T skL = true := by decide +kernel
theorem kKA : keysSK 65 7 minusBase SA.N SA.T skA = true := by decide +kernel

theorem kTreeA : allN 60 (fun k => Nat.beq (SA.T k) (pidn 65 7) ||
    allN 60 (ctreePt 65 7 60 k SA.T (WA k))) = true := by decide +kernel

theorem kT0A : Nat.beq (SA.T 0) (pidn 65 7) = true := by decide +kernel

theorem kFrameMem : allN 65 (fun k => memK 16 S0.T (CertificateChecks.KernelMinusEnum.ME.G k) ==
    isFrame k) = true := by decide +kernel

theorem kTrans : allN 15 (fun a => allN 15 fun b =>
    !(allN 120 fun j => !(Nat.beq (pg 7 (mask 7) (SL.T j) centArr[a]!) centArr[b]!))) = true := by
  decide +kernel

theorem kA : (allN 60 (fun j => !(Nat.beq (SA.T j) (XT 0))) &&
    allN 2 fun k => memK 120 SL.T (SA.G k)) = true := by decide +kernel

end CertificateChecks.KernelMinusFrame

end
