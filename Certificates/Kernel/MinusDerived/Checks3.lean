module

public import Certificates.Kernel.MinusDerived.ClassData
public import Certificates.Kernel.MinusDerived.Checks2
public import Certificates.Data.Kernel.HeAutK

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMinusL

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KC.BfsPin

@[expose] noncomputable def CD (k : ℕ) : ℕ := CB k

@[expose] noncomputable def CR (l : ℕ) : ℕ := CB (Nat.add 7800 l)

@[expose] noncomputable def CI (j : ℕ) : ℕ := CB (Nat.add 7815 j)

@[expose] noncomputable def labK (k : ℕ) : ℕ := Nat.land (CD k) 15

@[expose] noncomputable def witK (k : ℕ) : ℕ := Nat.land (Nat.shiftRight (CD k) 4) 8191

@[expose] noncomputable def cjK (k j : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (CD k) (Nat.add 17 (Nat.mul 13 j))) 8191

@[expose] noncomputable def cjOK (k : ℕ) : Bool :=
  allN 5 fun j => Nat.blt (cjK k j) 7800 &&
    Nat.beq (PL.T (cjK k j)) (pm (pm (PL.G j) (PL.T k)) (PL.T (CI j))) &&
    Nat.beq (labK (cjK k j)) (labK k)

@[expose] noncomputable def witOK (k : ℕ) : Bool :=
  Nat.blt (labK k) 15 && Nat.blt (witK k) 7800 &&
    Nat.beq (pm (PL.T (witK k)) (PL.T (CR (labK k)))) (pm (PL.T k) (PL.T (witK k)))

theorem kInvG : allN 5 (fun j => Nat.blt (CI j) 7800 &&
    Nat.beq (pm (PL.T (CI j)) (PL.G j)) (pidn 65 7)) = true := by decide +kernel

theorem kReps : allN 15 (fun l => Nat.blt (CR l) 7800 && Nat.beq (labK (CR l)) l) = true := by
  decide +kernel

theorem kCount : allN 15 (fun l => Nat.beq (CFSG.KC.HeAutK.cntR (fun k => Nat.beq (labK k) l) 0 7800)
    minusLSizes[l]!) = true := by decide +kernel

theorem kIdL : (Nat.beq (PL.T 0) (pidn 65 7) && Nat.beq (labK 0) 0) = true := by decide +kernel

theorem kWit : allN 7800 (fun k => witOK k) = true := by decide +kernel

theorem ch1383008j_0 : allN 1950 (fun i => cjOK i) = true := by decide +kernel
theorem ch1383008j_1 : allN 1950 (fun i => cjOK (1950 + i)) = true := by decide +kernel
theorem ch1383008j_2 : allN 1950 (fun i => cjOK (3900 + i)) = true := by decide +kernel
theorem ch1383008j_3 : allN 1950 (fun i => cjOK (5850 + i)) = true := by decide +kernel

end CertificateChecks.KernelMinusL
