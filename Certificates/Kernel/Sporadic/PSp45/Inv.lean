module

public import Certificates.Kernel.Sporadic.PSp45.Data
public import Certificates.Data.Kernel.SporSch.MathieuBT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.PSp45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.KS.SporSch.MOC

@[expose] def c6129W : List Int := [2, 1, 2, 2, 2, 1, 2, 1, 2]

@[expose] noncomputable def c6129WP : Nat :=
  abWordK 45 6 (mask 6) (pidn 45 6) (P45Q.S 0) (P45Q.SI 0) (P45Q.S 1) (P45Q.SI 1) c6129W

@[expose] noncomputable def c6129R3 : Nat := pcomp 45 6 (mask 6) (A45Q.S 2) c6129WP

@[expose] noncomputable def c6129A (wd : List Int) : Nat :=
  abWordK 45 6 (mask 6) (pidn 45 6) (P45Q.S 0) (P45Q.SI 0) (P45Q.S 1) (P45Q.SI 1) wd

@[expose] def c6129V0 : List Int := [1, 2, 2, 2, 2]

@[expose] def c6129V1 : List Int := [2, 2, 2, 1, 2, 1, 2, 2, 1]

@[expose] def c6129U0 : List Int := [1, 2, 2, 2, 2, 1, -2, -2, -2, -2, -1]

@[expose] def c6129U1 : List Int :=
  [2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, -1, -2, -2, -1, -2, -1, -2,
    -2, -2]

@[expose] noncomputable def c6129X0 : Nat := c6129A c6129U0

@[expose] noncomputable def c6129X1 : Nat := c6129A c6129U1

@[expose] noncomputable def c6129XL : List Nat := [c6129X0, c6129X1, A45Q.S 2, c6129R3]

theorem c6129ab : abOK c6129V0 = true ∧ abOK c6129V1 = true ∧ abOK c6129U0 = true ∧
    abOK c6129U1 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem c6129cj0 : Nat.beq (pcomp 45 6 (mask 6) (c6129A c6129V0) R0)
    (pcomp 45 6 (mask 6) c6129X0 (c6129A c6129V0)) = true := by quickRfl

theorem c6129cj1 : Nat.beq (pcomp 45 6 (mask 6) (c6129A c6129V1) R1)
    (pcomp 45 6 (mask 6) c6129X1 (c6129A c6129V1)) = true := by quickRfl

@[expose] def c6129CL : List Nat := [1152, 192, 96, 1440]

theorem c6129rep0 : repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI c6129X0
    1152 = true := by quickRfl

theorem c6129rep1 : repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI c6129X1
    192 = true := by quickRfl

theorem c6129rep2 : repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI (A45Q.S 2)
    96 = true := by quickRfl

theorem c6129rep3 : repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI c6129R3
    1440 = true := by quickRfl

theorem c6129d01 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI c6129X0
    c6129X1 = true := by quickRfl

theorem c6129d02 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI c6129X0
    (A45Q.S 2) = true := by quickRfl

theorem c6129d03 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI c6129X0
    c6129R3 = true := by quickRfl

theorem c6129d12 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI c6129X1
    (A45Q.S 2) = true := by quickRfl

theorem c6129d13 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI c6129X1
    c6129R3 = true := by quickRfl

theorem c6129d23 : distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI (A45Q.S 2)
    c6129R3 = true := by quickRfl

theorem c6129ord0 : ordC 45 6 (mask 6) c6129X0 = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c6129ord1 : ordC 45 6 (mask 6) c6129X1 = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c6129ord2 : ordC 45 6 (mask 6) (A45Q.S 2) = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c6129ord3 : ordC 45 6 (mask 6) c6129R3 = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c6129sum : sumAllK (ordK A45Q.LR 4) c6129CL 4 = 891 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelSpor.PSp45

end
