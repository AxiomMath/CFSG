module

public import Certificates.Kernel.Sporadic.PSp45.Data
public import Certificates.Data.Kernel.SporSch.MathieuBT
public meta import Certificates.Kernel.Sporadic.PSp45.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_cntord CertificateChecks.KernelSpor.A45X CertificateChecks.KernelSpor.A45Q 45 6
  CertificateChecks.KernelSpor.PSp45.SA CertificateChecks.KernelSpor.PSp45.baseA
  CertificateChecks.KernelSpor.PSp45.One CertificateChecks.KernelSpor.PSp45.oneM 2

namespace CertificateChecks.KernelSpor.PSp45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.KS.SporSch.MOC

@[expose] def c6129W : List Int := [2, 1, 2, 2, 2, 1, 2, 1, 2]

@[expose] noncomputable def c6129WP : Nat :=
  abWordK 45 6 (mask 6) (pidn 45 6) (P45Q.S 0) (P45Q.SI 0) (P45Q.S 1) (P45Q.SI 1) c6129W

@[expose] noncomputable def c6129R3 : Nat := pcomp 45 6 (mask 6) (A45Q.S 2) c6129WP

@[expose] noncomputable def c6129XL : List Nat := [R0, R1, A45Q.S 2, c6129R3]

@[expose] def c6129CL : List Nat := [1152, 192, 96, 1440]

theorem c6129rep0 : repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI R0 1152 =
    true := by quickRfl

theorem c6129rep1 : repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI R1 192 =
    true := by quickRfl

theorem c6129rep2 : repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI (A45Q.S 2)
    96 = true := by quickRfl

theorem c6129rep3 : repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI c6129R3
    1440 = true := by quickRfl

theorem c6129d01 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI R0 R1 =
    true := by quickRfl

theorem c6129d02 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI R0
    (A45Q.S 2) = true := by quickRfl

theorem c6129d03 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI R0
    c6129R3 = true := by quickRfl

theorem c6129d12 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI R1
    (A45Q.S 2) = true := by quickRfl

theorem c6129d13 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI R1
    c6129R3 = true := by quickRfl

theorem c6129d23 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI (A45Q.S 2)
    c6129R3 = true := by quickRfl

theorem c6129ord0 : ordC 45 6 (mask 6) R0 = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c6129ord1 : ordC 45 6 (mask 6) R1 = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c6129ord2 : ordC 45 6 (mask 6) (A45Q.S 2) = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c6129ord3 : ordC 45 6 (mask 6) c6129R3 = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c6129sum : sumAllK (ordK A45Q.LR 4) c6129CL 4 = A45X.CS.sum :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelSpor.PSp45

end
