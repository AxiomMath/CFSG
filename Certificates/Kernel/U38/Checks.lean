module

public import Certificates.Kernel.U38.Data
public import Certificates.Data.Kernel.K426K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.K426K

local notation "SX" G => siftOK 513 10 4 UX.LR UX.TRI UX.BP G
local notation "PM" => pcomp 513 10 (mask 10)
local notation "PI" => pinvS 513 10 (mask 10)
local notation "PW" => ppow 513 10 (mask 10) (pidn 513 10)

theorem szOK' : szOK 513 10 = true := by quickRfl

theorem permF : allN 28 (fun j => permB 513 10 (UF.F j)) = true := by quickRfl

theorem permH : allN 25 (fun j => permB 513 10 (UH.F j)) = true := by quickRfl

theorem nums : Nat.beq UQ.N 243 = true ∧ Nat.beq UQ.ng 3 = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem gensQ : allN 3 (fun j => Nat.beq (UQ.G j) (UF.F j)) = true := by quickRfl

theorem chainX : allN 7 (fun j => Nat.beq (UX.S j) (UH.F j)) = true ∧
    allN 4 (fun j => Nat.beq (UX.S (Nat.add 7 j)) (UH.F (Nat.add 21 j))) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem permX : allN 11 (fun j => permOK 513 10 (mask 10) (513 * 10) (UX.S j) (UX.SI j)) = true := by
  quickRfl

theorem kSylow : allN 3 (fun j =>
    SX (PM (UF.F j) (PW (PI (UH.F 7)) ([1, 2, 0].getD j 0)))) = true := by
  quickRfl

@[expose] noncomputable def classAt (i : Nat) : Bool :=
  !(Nat.beq (PW (UQ.T i) 3) (pidn 513 10) && !Nat.beq (UQ.T i) (pidn 513 10)) ||
    (Nat.blt (CW.getD i 0 / 16) 243 && Nat.blt (CW.getD i 0 % 16) 10 &&
      Nat.beq (PM (UQ.T (CW.getD i 0 / 16)) (PM (UQ.T i)
          (PI (UQ.T (CW.getD i 0 / 16)))))
        (UF.F (3 + CW.getD i 0 % 16)))

theorem kClass : allN 243 classAt = true := by quickRfl

@[expose] noncomputable def repAt (j : Nat) : Bool :=
  (SX (PM (UF.F ((13 + j))) (PW (PI (UH.F 7)) ([0, 2, 0, 0, 0, 2, 1, 0, 0, 1].getD j 0)))) &&
    Nat.blt (RW.getD j 0) 5 &&
    Nat.beq (PM (UF.F ((13 + j))) (PM (UF.F ((3 + j))) (PI (UF.F ((13 + j))))))
      (UF.F ((3 + [7, 8, 2, 0, 3].getD (RW.getD j 0) 0)))

theorem kReps : allN 10 repAt = true := by quickRfl

@[expose] noncomputable def frobAt (r : Nat) : Bool :=
  (SX (PM (UF.F ((23 + r))) (PW (PI (UH.F 7)) ([2, 2, 2, 1, 2].getD r 0)))) &&
    (Nat.beq (PM (UF.F ((23 + r))) (PM (PM (UH.F 8) (PM (UF.F ((3 + [7, 8, 2, 0, 3].getD r 0)))
        (PI (UH.F 8)))) (PI (UF.F ((23 + r))))))
      (UF.F ((3 + [7, 8, 2, 0, 3].getD r 0))) ||
    Nat.beq (PM (UF.F ((23 + r))) (PM (PM (UH.F 8) (PM (UF.F ((3 + [7, 8, 2, 0, 3].getD r 0)))
        (PI (UH.F 8)))) (PI (UF.F ((23 + r))))))
      (PI (UF.F ((3 + [7, 8, 2, 0, 3].getD r 0)))))

theorem kFrob : allN 5 frobAt = true := by quickRfl

theorem kLast : (SX (PW (UH.F 7) 3)) = true ∧
    (SX (PM (PM (UH.F 8) (PM (UH.F 7) (PI (UH.F 8)))) (PW (PI (UH.F 7)) 2))) = true ∧
    (SX (PM (PM (PI (UH.F 8)) (PM (UH.F 7) (UH.F 8))) (PW (PI (UH.F 7)) 2))) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelU38

end
