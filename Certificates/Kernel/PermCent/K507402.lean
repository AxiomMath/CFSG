module

public import Certificates.Data.Kernel.PermCent.Sp6BTwin
public import Certificates.Kernel.PermCent.Sp6BLay
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.Sp6B
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

@[expose] noncomputable def perfK (c : CV 36) (k : Nat) : Bool :=
  !commAllC c (memberElemsC L0C (wsC.getD k 1)) ||
    (memberElemsC L0C (wsC.getD k 1)).all fun x => perfWords.any fun e =>
      e.getD 0 0 == k && commAllC c (memberElemsC L0C (wsC.getD (e.getD 1 0) 1)) &&
        commAllC c (memberElemsC L0C (wsC.getD (e.getD 2 0) 1)) &&
        (memberElemsC L0C (wsC.getD (e.getD 1 0) 1)).any fun y =>
          (memberElemsC L0C (wsC.getD (e.getD 2 0) 1)).any fun z =>
            decide (y * z * y⁻¹ * z⁻¹ = x)

@[expose] noncomputable def perfQ (c : CV 36) : Bool := (List.range wsC.length).all (perfK c)

theorem kRlen : (List.range wsC.length).length ≤ 3 * 210 := by decide +kernel

theorem kQ0_0 : (((List.range wsC.length).drop (0 * 210)).take 210).all (perfK lay0) = true := by
  decide +kernel

theorem kQ0_1 : (((List.range wsC.length).drop (1 * 210)).take 210).all (perfK lay0) = true := by
  decide +kernel

theorem kQ0_2 : (((List.range wsC.length).drop (2 * 210)).take 210).all (perfK lay0) = true := by
  decide +kernel

theorem kQ1_0 : (((List.range wsC.length).drop (0 * 210)).take 210).all (perfK lay1) = true := by
  decide +kernel

theorem kQ1_1 : (((List.range wsC.length).drop (1 * 210)).take 210).all (perfK lay1) = true := by
  decide +kernel

theorem kQ1_2 : (((List.range wsC.length).drop (2 * 210)).take 210).all (perfK lay1) = true := by
  decide +kernel

theorem kQ2_0 : (((List.range wsC.length).drop (0 * 210)).take 210).all (perfK lay2) = true := by
  decide +kernel

theorem kQ2_1 : (((List.range wsC.length).drop (1 * 210)).take 210).all (perfK lay2) = true := by
  decide +kernel

theorem kQ2_2 : (((List.range wsC.length).drop (2 * 210)).take 210).all (perfK lay2) = true := by
  decide +kernel

theorem kQ0 : perfQ lay0 = true :=
  CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 210 3 kRlen fun j hj =>
    match j, hj with
    | 0, _ => kQ0_0
    | 1, _ => kQ0_1
    | 2, _ => kQ0_2
    | k + 3, h => absurd h (by omega)

theorem kQ1 : perfQ lay1 = true :=
  CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 210 3 kRlen fun j hj =>
    match j, hj with
    | 0, _ => kQ1_0
    | 1, _ => kQ1_1
    | 2, _ => kQ1_2
    | k + 3, h => absurd h (by omega)

theorem kQ2 : perfQ lay2 = true :=
  CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 210 3 kRlen fun j hj =>
    match j, hj with
    | 0, _ => kQ2_0
    | 1, _ => kQ2_1
    | 2, _ => kQ2_2
    | k + 3, h => absurd h (by omega)

theorem k507402_ne : layC.isEmpty = false := by decide +kernel

theorem k507402 : twinPerfC = true := by
  show (!layC.isEmpty && layC.all perfQ) = true
  rw [k507402_ne, all_layC kQ0 kQ1 kQ2]
  rfl

end CertificateChecks.KernelPermCent
