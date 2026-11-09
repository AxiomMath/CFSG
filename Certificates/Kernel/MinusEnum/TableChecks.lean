module

public import Certificates.Kernel.MinusEnum.Data
public import Certificates.Data.Kernel.BfsPinKeys
public import Certificates.Data.Kernel.BfsPinSeed
public import Certificates.Kernel.MinusEnum.FacData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMinusEnum

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.Prim
open CFSG.KLie.CT (fget)

@[expose] noncomputable def cmpM (p q : ℕ) : ℕ := pcomp 65 7 (mask 7) p q

@[expose] def seedS : List ℕ := [0, 1, 3, 17]

@[expose] def derivD : List ℕ := [128, 2177, 2179, 2947, 145, 273, 2961, 7569, 2944, 3456, 6016,
  7552, 2433, 2689, 5633, 6017, 5634, 6018, 2435, 2563, 2691, 3075, 3459, 3587, 5379, 5507, 5635,
  6019, 6531, 6659, 2577, 3601, 3857, 3985, 5009, 5137, 5521, 6673, 7185, 8209, 2581, 5013, 5141,
  5525, 6677, 7189, 8213, 791, 1943, 4119, 4375, 4631, 5399, 5655, 6423, 7063, 7319, 7831, 1304,
  6296, 1179]

@[expose] noncomputable def facK (b : ℕ) : ℕ := fget fKK b 455

@[expose] noncomputable def facR (a : ℕ) : ℕ := fget fRR a 455

@[expose] noncomputable def facC (c : ℕ) : ℕ := fget fKC c 8

@[expose] noncomputable def facT (c b : ℕ) : ℕ := fget fKT (Nat.add (Nat.mul c 240) b) 8

@[expose] noncomputable def facS (o s : ℕ) : Bool := allN 65 fun a =>
  Nat.blt (fget fRA (Nat.add o a) 8) 65 && Nat.blt (fget fRB (Nat.add o a) 8) 240 &&
    Nat.beq (cmpM (ME.G s) (facR a))
      (cmpM (facR (fget fRA (Nat.add o a) 8)) (facK (fget fRB (Nat.add o a) 8)))

theorem kPermG : allN 65 (fun k => permOK 65 7 (mask 7) (Nat.mul 65 7) (ME.G k)
    (pinvS 65 7 (mask 7) (ME.G k))) = true := by decide +kernel

theorem kTabInvol : allN 65 (fun i => allN 65 fun j =>
    Nat.beq (pg 7 (mask 7) (ME.G i) (pg 7 (mask 7) (ME.G i) j)) j) = true := by decide +kernel

theorem kTabKey : allN 65 (fun i => allN 65 fun j =>
    Nat.beq i j || !Nat.beq (pkeyK 65 7 minusBase (ME.G i)) (pkeyK 65 7 minusBase (ME.G j))) =
      true := by decide +kernel

@[expose] noncomputable def conjRowM (i : ℕ) : Bool := allN 65 fun j =>
  Nat.beq (ME.G (pg 7 (mask 7) (ME.G i) j)) (cmpM (ME.G i) (cmpM (ME.G j) (ME.G i)))

theorem kTabConj : (conjRowM 0 && conjRowM 1 && conjRowM 3 && conjRowM 17) = true := by
  decide +kernel

theorem kDeriv : Nat.beq (derivK 7 ME.G derivD (seedMask seedS)) (2 ^ 65 - 1) = true := by
  decide +kernel

theorem kFacCan : allN 240 (fun b => canonK 65 7 (mask 7) (65 * 7) (facK b)) &&
    allN 65 (fun a => canonK 65 7 (mask 7) (65 * 7) (facR a)) = true := by decide +kernel

theorem kFacK : allN 3 (fun c => Nat.blt (facC c) 240 && allN 240 fun b =>
    Nat.blt (facT c b) 240 && Nat.beq (cmpM (facK (facC c)) (facK b)) (facK (facT c b))) &&
    allN 240 (fun b => Nat.beq b 0 || (Nat.blt (fget fKP b 8) b && Nat.blt (fget fKI b 8) 3 &&
      Nat.beq (facT (fget fKI b 8) (fget fKP b 8)) b)) && Nat.beq (facC 0) 0 = true := by
  decide +kernel

theorem kFacT0 : Nat.beq (ME.T 0) (cmpM (facR 0) (facK 0)) = true := by decide +kernel

theorem kFacS0 : facS 0 0 = true := by decide +kernel
theorem kFacS1 : facS 65 1 = true := by decide +kernel
theorem kFacS2 : facS 130 3 = true := by decide +kernel
theorem kFacS3 : facS 195 17 = true := by decide +kernel

end CertificateChecks.KernelMinusEnum

end
