module

public import Certificates.Kernel.MinusEnum.Data
public import Certificates.Data.Kernel.BfsPinKeys
public import Certificates.Data.Kernel.BfsPinSeed

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMinusEnum

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] noncomputable def cmpM (p q : ℕ) : ℕ := pcomp 65 7 (mask 7) p q

@[expose] def seedS : List ℕ := [0, 1, 3, 17]

@[expose] def derivD : List ℕ := [128, 2177, 2179, 2947, 145, 273, 2961, 7569, 2944, 3456, 6016,
  7552, 2433, 2689, 5633, 6017, 5634, 6018, 2435, 2563, 2691, 3075, 3459, 3587, 5379, 5507, 5635,
  6019, 6531, 6659, 2577, 3601, 3857, 3985, 5009, 5137, 5521, 6673, 7185, 8209, 2581, 5013, 5141,
  5525, 6677, 7189, 8213, 791, 1943, 4119, 4375, 4631, 5399, 5655, 6423, 7063, 7319, 7831, 1304,
  6296, 1179]

@[expose] noncomputable def seedM (i : ℕ) : Bool := seedPt 65 7 15600 ME.G ME.T ME.E i seedS

theorem kPermG : allN 65 (fun k => permOK 65 7 (mask 7) (Nat.mul 65 7) (ME.G k)
    (pinvS 65 7 (mask 7) (ME.G k))) = true := by decide +kernel

theorem kTabInvol : allN 65 (fun i => allN 65 fun j =>
    Nat.beq (pg 7 (mask 7) (ME.G i) (pg 7 (mask 7) (ME.G i) j)) j) = true := by decide +kernel

theorem kTabKey : allN 65 (fun i => allN 65 fun j =>
    Nat.beq i j || !Nat.beq (pkeyK 65 7 minusBase (ME.G i)) (pkeyK 65 7 minusBase (ME.G j))) =
      true := by decide +kernel

theorem kTabConj : allN 65 (fun i => allN 65 fun j =>
    Nat.blt (pg 7 (mask 7) (ME.G i) j) 65 &&
      Nat.beq (ME.G (pg 7 (mask 7) (ME.G i) j)) (cmpM (ME.G i) (cmpM (ME.G j) (ME.G i)))) =
        true := by decide +kernel

theorem kDeriv : Nat.beq (derivK 7 ME.G derivD (seedMask seedS)) (2 ^ 65 - 1) = true := by
  decide +kernel

theorem ch1383006s_0 : allN 3900 (fun i => seedM i) = true := by decide +kernel
theorem ch1383006s_1 : allN 3900 (fun i => seedM (3900 + i)) = true := by decide +kernel
theorem ch1383006s_2 : allN 3900 (fun i => seedM (7800 + i)) = true := by decide +kernel
theorem ch1383006s_3 : allN 3900 (fun i => seedM (11700 + i)) = true := by decide +kernel

end CertificateChecks.KernelMinusEnum

end
