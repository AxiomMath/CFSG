module

public import Certificates.Kernel.G24Cls.Pack27205
public import Certificates.Kernel.G24Tri.Pack27206
public import Certificates.Kernel.G24Tri.Chain27206
public import Certificates.Data.Kernel.G24Rigid
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CertificateChecks.KernelG24.Rigid27205

open CFSG.KC.Enum CFSG.KC.G24Key CFSG.KC.G24Rigid CertificateChecks.KernelG24.Tri27206

@[expose] noncomputable def sgS (l : Nat) : Nat := SG (Nat.land l (nat_lit 15))

@[expose] noncomputable def sgSI (l : Nat) : Nat := SGI (Nat.land l (nat_lit 15))

@[expose] noncomputable def zK (k p : Nat) : Nat := eK sgS sgSI SP SL (nat_lit 5) (PK 6) k p

@[expose] noncomputable def fK (k : Nat) : Nat → Nat → Nat := tlet (zK k) BB

@[expose] noncomputable def keyS (k : Nat) : Nat := keyK sgS sgSI SP SL (nat_lit 5) (PK 6) k

@[expose] def tst : Nat → List (List Nat × Nat)
  | 1 => [([0, 1], 3)]
  | 2 => [([0, 1], 3), ([0, 2], 3), ([0, 1, 2], 8), ([0, 2, 1], 8), ([1, 0, 2], 8),
      ([0, 1, 2, 1], 4), ([0, 2, 1, 2], 4)]
  | 3 => [([0, 1], 5), ([0, 2], 5), ([0, 1, 2], 5), ([0, 2, 1], 5), ([1, 0, 2], 5),
      ([0, 1, 2, 1], 2), ([0, 2, 1, 2], 2), ([0, 3], 3), ([0, 1, 3], 6), ([0, 3, 1], 6),
      ([0, 2, 3], 15), ([0, 3, 2], 15), ([1, 0, 3], 6), ([2, 0, 3], 15), ([0, 1, 2, 3], 6),
      ([0, 3, 2, 1], 6)]
  | _ => []

@[expose] def zero27205 (_ : Nat) : Nat := 0

theorem kGen : (ptEqK (SG 0) (ap (LC.S 0)) && ptEqK (SG 1) (ap (LC.S 1)) && slpK SG SLP 16 &&
    invK SG SGI 16) = true := by
  quickRfl
theorem kBase : (Nat.beq (NB 0) 0 && allN 4 (fun j => Nat.blt (NB j) 4095) &&
    allN 4 (fun j => ptEqK (BB j) (zK (NB j)))) = true := by quickRfl
theorem kWords : (allN 3 (fun t => Nat.beq (wpB BB WX 847 t) (ap (LC.S 0) t)) &&
    allN 3 (fun t => Nat.beq (wpB BB WY 24 t) (ap (LC.S 1) t))) = true := by quickRfl
theorem kOwn : (ownK (tlet (ap (BB 1)) BB) (tst 1) && ownK (tlet (ap (BB 2)) BB) (tst 2) &&
    ownK (tlet (ap (BB 3)) BB) (tst 3)) = true := by quickRfl
theorem kKeys : sortedK keyS OS 4095 = true := by quickRfl
theorem kRef1 : levK fK (tst 1) (t12 R1) zero27205 4095 = true := by quickRfl
theorem kRef2 : levK fK (tst 2) (t12 R2) (t12 R1) 4095 = true := by quickRfl
theorem kRef3 : levK fK (tst 3) (t12 R3) zero27205 4095 = true := by quickRfl
theorem kCnt : (Nat.ble (cntK (t12 R1) zero27205 4095) 1024 &&
    Nat.ble (cntK (t12 R2) (t12 R1) 4095) 60 &&
    Nat.ble (cntK (t12 R3) zero27205 4095) 2) = true := by quickRfl

end CertificateChecks.KernelG24.Rigid27205

end
