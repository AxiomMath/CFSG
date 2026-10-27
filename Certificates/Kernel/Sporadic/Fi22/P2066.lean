module

public import Certificates.Kernel.Sporadic.Fi22.H2066c0
public import Certificates.Kernel.Sporadic.Fi22.H2066c1
public import Certificates.Kernel.Sporadic.Fi22.H2066c2
public import Certificates.Kernel.Sporadic.Fi22.H2066c3
public import Certificates.Kernel.Sporadic.Fi22.H2066c4
public import Certificates.Kernel.Sporadic.Fi22.E2065
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C2066

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

abbrev B : Array Nat := #[0, 1, 2, 3, 6, 4]

@[expose] noncomputable def bindK (PS : Nat → Nat) (kS st : Nat) : Bool :=
  allN kS (fun j => Nat.beq (PS j) (Fi22CentT.L (Nat.add st j)))

@[expose] noncomputable def baseK (BP : Nat) : Bool :=
  allN 6 (fun t => Nat.beq B[t]! (pg 12 (mask 12) BP t))

@[expose] noncomputable def inPK (PS : Nat → Nat) (kS : Nat) : Bool :=
  bAnd(allN kS (fun j => Fi22X.cn (PS j)), allN kS (fun j => Fi22X.siftP (PS j)))

@[expose] noncomputable def commK (PS : Nat → Nat) (kO cs : Nat) : Bool :=
  bAnd(Fi22X.cn (Fi22ExtT.L (Nat.add 21 cs)),
    allN kO (fun j => Nat.beq (Fi22X.c (PS j) (Fi22ExtT.L (Nat.add 21 cs)))
      (Fi22X.c (Fi22ExtT.L (Nat.add 21 cs)) (PS j))))

theorem b0 : bindK Fi22H0.S 19 0 = true := by quickRfl
theorem b1 : bindK Fi22H1.S 16 19 = true := by quickRfl
theorem b2 : bindK Fi22H2.S 9 35 = true := by quickRfl
theorem b3 : bindK Fi22H3.S 19 44 = true := by quickRfl
theorem b4 : bindK Fi22H4.S 16 63 = true := by quickRfl
theorem p0 : baseK Fi22H0.BP = true := by quickRfl
theorem p1 : baseK Fi22H1.BP = true := by quickRfl
theorem p2 : baseK Fi22H2.BP = true := by quickRfl
theorem p3 : baseK Fi22H3.BP = true := by quickRfl
theorem p4 : baseK Fi22H4.BP = true := by quickRfl
theorem m0 : commK Fi22H0.S 12 0 = true := by quickRfl
theorem m1 : commK Fi22H1.S 9 1 = true := by quickRfl
theorem m2 : commK Fi22H2.S 3 3 = true := by quickRfl
theorem m3 : commK Fi22H3.S 9 4 = true := by quickRfl
theorem m4 : commK Fi22H4.S 9 5 = true := by quickRfl
theorem s0 : inPK Fi22H0.S 19 = true := by quickRfl
theorem s1 : inPK Fi22H1.S 16 = true := by quickRfl
theorem s2 : inPK Fi22H2.S 9 = true := by quickRfl
theorem s3 : inPK Fi22H3.S 19 = true := by quickRfl
theorem s4 : inPK Fi22H4.S 16 = true := by quickRfl
theorem o0 : ((List.range 6).map fun i => rcnt (Fi22H0.LR i)).prod = fi22CentOrders.getD 0 0 := by
  decide +kernel
theorem o1 : ((List.range 6).map fun i => rcnt (Fi22H1.LR i)).prod = fi22CentOrders.getD 1 0 := by
  decide +kernel
theorem o2 : ((List.range 6).map fun i => rcnt (Fi22H2.LR i)).prod = fi22CentOrders.getD 2 0 := by
  decide +kernel
theorem o3 : ((List.range 6).map fun i => rcnt (Fi22H3.LR i)).prod = fi22CentOrders.getD 3 0 := by
  decide +kernel
theorem o4 : ((List.range 6).map fun i => rcnt (Fi22H4.LR i)).prod = fi22CentOrders.getD 4 0 := by
  decide +kernel

end CertificateChecks.KernelSpor.Fi22C2066

end
