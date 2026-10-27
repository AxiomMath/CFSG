module

public import Certificates.Kernel.S63K.OData
public import Certificates.Data.Kernel.S63K.Low
public import Certificates.Data.Kernel.MergeTG
public import Certificates.Data.D4HexOverWords
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.OM

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KC.MergeG CFSG.D4Hex CertificateChecks.KernelS63

@[expose] noncomputable def mD (o : Nat) : Nat := dg (OD.D 30) o
@[expose] noncomputable def m4 (o : Nat) : Nat :=
  (((0 * 16 + mD (o + 0)) * 16 + mD (o + 1)) * 16 + mD (o + 2)) * 16 + mD (o + 3)
@[expose] noncomputable def off (j : Nat) : Nat := [0, 11, 54, 212, 540, 1015, 1770, 2966, 4046].getD j 0
@[expose] noncomputable def RI (j k : Nat) : Nat := (0 * 16 + mD (9 * (off j + k) + 0)) % 8
@[expose] noncomputable def RU (j k : Nat) : Nat := m4 (9 * (off j + k) + 1) % 7371
@[expose] noncomputable def RV (j k : Nat) : Nat := m4 (9 * (off j + k) + 5) % 7371

@[expose] noncomputable def mOK (j : Nat) : Bool :=
  mergeTCKG 7371 13 8 OD.D 0 (ovReps.getD (j + 3) 0) (ovMergeLens.getD j 0) (ovMergeLens.getD j 0) 1
    (RI j) (RU j) (RV j) (OD.D (34 + 4 * j)) (OD.D (35 + 4 * j)) (fun s => OD.D (36 + 4 * j + s))
    [1, 3]

theorem ch4238T : bAnd(lowK OD.MC 0 (OD.D 30), Nat.beq OD.MC.length 40149) = true := by quickRfl

theorem m0 : mOK 0 = true := by quickRfl
theorem m1 : mOK 1 = true := by quickRfl
theorem m2 : mOK 2 = true := by quickRfl
theorem m3 : mOK 3 = true := by quickRfl
theorem m4' : mOK 4 = true := by quickRfl
theorem m5 : mOK 5 = true := by quickRfl
theorem m6 : mOK 6 = true := by quickRfl
theorem m7 : mOK 7 = true := by quickRfl
theorem m8 : mOK 8 = true := by quickRfl

end CertificateChecks.KernelS63.OM

end
