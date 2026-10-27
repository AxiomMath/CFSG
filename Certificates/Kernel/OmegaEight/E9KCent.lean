module

public import Certificates.Kernel.OmegaEight.E9KData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.E9K

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.PGrp
open CertificateChecks.KernelO8

@[expose] noncomputable def commK (g : Nat) : Nat :=
  ((List.range 81).filter fun i => Nat.beq (pm g (E9D.T i)) (pm (E9D.T i) g)).length

@[expose] noncomputable def centK (b g : Nat) : Bool :=
  allN 81 (fun i => !Nat.beq g (E9D.T i)) && Nat.ble (commK g) b

theorem cent : centK 9 (posWordK 360 9 E9Q.G [1]) = true := by quickRfl

end CertificateChecks.KernelO8.E9K

end
