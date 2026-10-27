
module

public import Certificates.Data.Kernel.J4Count
public import Certificates.Kernel.SporSch.J4S.NoCK
public import Certificates.Kernel.SporSch.J4S.Orbits
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.KC.Enum CFSG.KC.J4Count CFSG.KC.J4Q CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4NoCK

@[expose] def RC : List Nat := [2048, 2, 1, 1, 16, 512, 128]

@[expose] noncomputable def basisOK (BS PS : List (List Nat)) (l : Nat) : Bool :=
  bAnd(Nat.beq (List.length (getL PS l)) (List.length (getL BS l)),
  bAnd(Nat.beq (Nat.shiftLeft 1 (List.length (getL BS l))) (getN 0 RC l),
  bAnd(allL (getL BS l) (fun b => bAnd(Nat.blt b 2048, Nat.beq (etaK (J4RV l) b) (J4RV l))),
    allN (Nat.shiftLeft 1 (List.length (getL BS l)))
      (fun m => Nat.beq (decode (getL PS l) (combo (getL BS l) m)) m))))

@[expose] noncomputable def cntZ (BS PS : List (List Nat)) (l : Nat) : Nat :=
  cntK 1771 (fun i => Nat.beq (combo (getL BS l) (decode (getL PS l) (J4O1.PT i))) (J4O1.PT i))

theorem basis_ok : allN 7 (basisOK BS PS) = true := by quickRfl

theorem cnt_ok : allN 7 (fun l => Nat.beq (cntZ BS PS l) (getN 0 CZ l)) = true := by quickRfl

theorem neg_basis : notB (basisOK [[], [1721], [], [], [], [], []] PS 1) = true := by quickRfl

theorem neg_pivot : notB (basisOK BS [[], [], [], [], [8, 6, 9, 10], [], []] 4) = true := by
  quickRfl

theorem neg_size : notB (basisOK [[], [], [], [], [], [], [2, 29, 37, 64, 384, 525]]
    [[], [], [], [], [], [], [1, 4, 5, 6, 8, 9]] 6) = true := by quickRfl

theorem neg_cnt : notB (Nat.beq (cntZ BS PS 4) 16) = true := by quickRfl

theorem neg_basis_z : notB (basisOK [[], [1], [], [], [], [], []] [[], [0], [], [], [], [], []] 1) =
    true := by quickRfl

end CertificateChecks.KernelJ4Count

end
