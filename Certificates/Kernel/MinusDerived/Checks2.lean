module

public import Certificates.Kernel.MinusDerived.Data
public import Certificates.Kernel.MinusDerived.Local
public import Certificates.Kernel.MinusEnum.Data
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.PermPinK
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Certificates.Kernel.Lie.CT.Core

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMinusL

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KC.BfsPin CFSG.KC.PermPinK CertificateChecks.KernelMinusEnum
open CFSG.KLie.CT (anyN)

@[expose] noncomputable def pm (p q : ℕ) : ℕ := pcomp 65 7 (mask 7) p q

@[expose] def jOf (k : ℕ) : ℕ :=
  cond (Nat.beq k 0) 1 (cond (Nat.beq k 1) 3 (cond (Nat.beq k 2) 4 (cond (Nat.beq k 3) 10 11)))

@[expose] noncomputable def centPt (i : ℕ) : Bool :=
  !(allN 5 fun k => Nat.beq (pm (ME.T i) (PL.G k)) (pm (PL.G k) (ME.T i))) ||
    Nat.beq (ME.T i) (pidn 65 7)

theorem kCanL : allN 7800 (fun j => canonK 65 7 (mask 7) (Nat.mul 65 7) (PL.T j)) = true := by
  decide +kernel

theorem kCanG : (allN 5 (fun k => canonK 65 7 (mask 7) (Nat.mul 65 7) (PL.G k)) &&
    allN 4 (fun k => canonK 65 7 (mask 7) (Nat.mul 65 7) (LX k))) = true := by decide +kernel

theorem kRefl : allN 7800 (fun j => allN 65 fun i => !Nat.beq (PL.T j) (ME.G i)) = true := by
  decide +kernel

theorem kGensP : allN 5 (fun k => Nat.beq (PL.G k) (pm (ME.G 0) (ME.G (jOf k)))) = true := by
  decide +kernel

theorem kBindX : (Nat.beq locArr.size 4 &&
    allN 4 fun k => bindArrK locArr[k]! 65 7 (LX k)) = true := by decide +kernel

theorem kPermX : allN 4 (fun k => permOK 65 7 (mask 7) (Nat.mul 65 7) (LX k)
    (pinvS 65 7 (mask 7) (LX k))) = true := by decide +kernel

theorem kMemX : allN 4 (fun k => memK 7800 PL.T (LX k)) = true := by decide +kernel

theorem kTrans : allN 65 (fun i => anyN 15600 fun j => Nat.beq (pg 7 (mask 7) (ME.T j) 0) i) = true := by
  decide +kernel

theorem ch1383008c_0 : allN 3900 (fun i => centPt i) = true := by decide +kernel
theorem ch1383008c_1 : allN 3900 (fun i => centPt (3900 + i)) = true := by decide +kernel
theorem ch1383008c_2 : allN 3900 (fun i => centPt (7800 + i)) = true := by decide +kernel
theorem ch1383008c_3 : allN 3900 (fun i => centPt (11700 + i)) = true := by decide +kernel

end CertificateChecks.KernelMinusL
