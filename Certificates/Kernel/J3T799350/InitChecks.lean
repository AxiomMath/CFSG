module

public import Certificates.Kernel.J3T799350.Data
public import Certificates.Kernel.SporSch.J3K426.Checks
public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Data.Kernel.Spor.RawOrbOut
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelJ3T799350
  "Certificates/Kernel/J3T799350/data/init.json.gz" 534 5021248670786527339 (iwords : List (List Nat))

namespace CertificateChecks.KernelJ3T799350

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSporSch
  CertificateChecks.KernelSpor

theorem rt0 : Nat.beq (RT 0) (PJ3.S 0) = true := by quickRfl
theorem rt1 : Nat.beq (RT 1) (PJ3.S 1) = true := by quickRfl
theorem rt2 : Nat.beq (RT 2) (J3CentP 0) = true := by quickRfl
theorem rt3 : Nat.beq (RT 3) (J3KT.D 0) = true := by quickRfl
theorem rt4 : Nat.beq (RT 4) (J3KT.D 1) = true := by quickRfl
theorem rt5 : Nat.beq (RT 5) J3KT.G = true := by quickRfl
theorem rt6 : Nat.beq (RT 6) (J3CentP 9) = true := by quickRfl
theorem rt7 : Nat.beq (RT 7) (J3CentP 10) = true := by quickRfl
theorem rt8 : Nat.beq (RT 8) (J3CentP 11) = true := by quickRfl
theorem rt9 : Nat.beq (RT 9) (J3CentP 12) = true := by quickRfl
theorem rt10 : Nat.beq (RT 10) (J3CentP 13) = true := by quickRfl
theorem rt11 : Nat.beq (RT 11) (J3CentP 14) = true := by quickRfl
theorem rt12 : Nat.beq (RT 12) (J3KT.F 33) = true := by quickRfl
theorem rt13 : Nat.beq (RT 13) (J3KT.F 34) = true := by quickRfl
theorem rt14 : Nat.beq (RT 14) (J3KT.F 35) = true := by quickRfl
theorem rt15 : Nat.beq (RT 15) (J3KT.F 36) = true := by quickRfl
theorem rt16 : Nat.beq (RT 16) J3KT.X0 = true := by quickRfl
theorem rt17 : Nat.beq (RT 17) J3KT.U = true := by quickRfl
theorem rt18 : Nat.beq (RT 18) J3KT.V = true := by quickRfl

theorem canon : allBlk 0 (fun r => canonK 6156 13 (mask 13) (6156 * 13) (RT r)) 19 = true := by
  quickRfl

@[expose] def ofCode (c : Nat) : Int :=
  Bool.rec (Int.ofNat (Nat.shiftRight c 1)) (Int.negSucc (Nat.sub (Nat.shiftRight c 1) 1))
    (Nat.beq (Nat.land c 1) 1)

@[expose] noncomputable def iwOK (r : Nat) : Bool :=
  wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5
    ((List.getD iwords (r - 3) []).map ofCode) (RT r)

theorem iw0 : allBlk 3 iwOK 8 = true := by quickRfl
theorem iw1 : allBlk 11 iwOK 8 = true := by quickRfl

theorem uOut : outK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) PJ3.S PJ3.SI 5 PJ3.BP 1 (PJ3.LR 1)
    [-2, -1, -2, 3, -2, -4, 3] (RT 2) = true := by quickRfl

theorem n_iw : (iwOK 2).not = true := by quickRfl

end CertificateChecks.KernelJ3T799350

end
