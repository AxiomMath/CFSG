module

public import Certificates.Kernel.Item434.McLData
public import Certificates.Kernel.Item434.McLQ
public import Certificates.Kernel.Census.McLChain
public import Certificates.Data.Kernel.B3S3K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelItem434

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K (cm pw)

@[expose] noncomputable def cjN (h t : ℕ) : ℕ := cm 275 9 (cm 275 9 h t) (pinvS 275 9 (mask 9) h)

@[expose] noncomputable def idM : ℕ := pidn 275 9

@[expose] noncomputable def siftM (G : ℕ) : Bool :=
  Nat.beq (Nat.shiftRight G (275 * 9)) 0 && allN 275 (fun t => Nat.blt (pg 9 (mask 9) G t) 275) &&
    siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) KernelCensus.McLC.LR KernelCensus.McLC.TRI
      KernelCensus.McLC.BP 5 0 G

@[expose] noncomputable def dK (u : ℕ) : ℕ :=
  cm 275 9 (cm 275 9 (cm 275 9 (pw 275 9 (MH.F 0) (u % 3)) (pw 275 9 (MH.F 1) (u / 3 % 3)))
    (pw 275 9 (MH.F 2) (u / 9 % 3))) (pw 275 9 (MH.F 3) (u / 27 % 3))

@[expose] noncomputable def p9K (u : ℕ) : ℕ :=
  cm 275 9 (cm 275 9 (cm 275 9 (pw 275 9 (DP 34) (u % 3)) (pw 275 9 (DP 3) (u / 3 % 3)))
    (pw 275 9 (DP 38) (u / 9 % 3))) (pw 275 9 (DP 35) (u / 27 % 3))

@[expose] noncomputable def lineK (W : ℕ → ℕ) (j : ℕ) : Bool :=
  (Nat.blt (W j) 81 && Nat.beq (K3.F (4 + j)) (DP (W j))) ||
    (Nat.blt ((W j - 81) / 24) EQ.N &&
      Nat.beq (cjN (EQ.T ((W j - 81) / 24)) (K3.F (4 + j))) (MH.F (4 + (W j - 81) % 24)) &&
      Nat.beq (cjN (EQ.T ((W j - 81) / 24)) (MH.F 0)) (MH.F 0) && siftM (EQ.T ((W j - 81) / 24)))

@[expose] noncomputable def conjK (U Z : ℕ → ℕ) (i : ℕ) : Bool :=
  siftM (MH.F (28 + i)) && permB 275 9 (MH.F (4 + i)) && Nat.blt (U i) 81 &&
    Nat.beq (cjN (MH.F (28 + i)) (MH.F (4 + i))) (DP (U i)) && Nat.blt (Z i) 81 &&
    Nat.beq (cjN (MH.F (28 + i)) (MH.F 0)) (DP (Z i))

theorem kW : szOK 275 9 = true := by quickRfl

theorem kMHp : allN 52 (fun k => permB 275 9 (MH.F k)) = true := by quickRfl
theorem kM9p : allN 3 (fun k => permB 275 9 (M9.F k)) = true := by quickRfl
theorem kK3p : allN 152 (fun k => permB 275 9 (K3.F k)) = true := by quickRfl

theorem kEQG : allN 4 (fun j => Nat.beq (EQ.G j) (K3.F j)) = true := by quickRfl
theorem kEQn : Nat.beq EQ.ng 4 = true ∧ Nat.beq EQ.N 729 = true := ⟨by quickRfl, by quickRfl⟩

theorem kDP : allN 81 (fun u => Nat.beq (DP u) (dK u)) = true := by quickRfl
theorem kP9 : allN 81 (fun u => Nat.beq (P9 u) (p9K u)) = true := by quickRfl

theorem kZ : Nat.beq (MH.F 0) idM = false ∧
    allN 4 (fun k => Nat.beq (cm 275 9 (MH.F 0) (K3.F k)) (cm 275 9 (K3.F k) (MH.F 0))) = true :=
  ⟨by decide +kernel, by quickRfl⟩

theorem kD1 : allN 4 (fun k => siftM (MH.F k)) = true := by quickRfl
theorem kD2 : allN 4 (fun k => Nat.beq (pw 275 9 (MH.F k) 3) idM) = true := by quickRfl
theorem kD3 : allN 4 (fun k => allN 4 fun l =>
    Nat.beq (cm 275 9 (MH.F k) (MH.F l)) (cm 275 9 (MH.F l) (MH.F k))) = true := by quickRfl
theorem kD4 : allN 81 (fun u => allN 81 fun v => u == v || !Nat.beq (DP u) (DP v)) = true := by
  quickRfl

theorem kL0 : allN 37 (fun j => lineK LW j) = true := by quickRfl
theorem kL1 : allN 37 (fun j => lineK LW (37 + j)) = true := by quickRfl
theorem kL2 : allN 37 (fun j => lineK LW (74 + j)) = true := by quickRfl
theorem kL3 : allN 37 (fun j => lineK LW (111 + j)) = true := by quickRfl

theorem kC : allN 24 (fun i => conjK CU CZ i) = true := by quickRfl

theorem k9S : allN 3 (fun k => siftM (M9.F k)) = true := by quickRfl
theorem k9R : (Nat.beq (cjN (M9.F 0) (DP 34)) (DP 34) && Nat.beq (cjN (M9.F 0) (DP 3)) (DP 3) &&
    Nat.beq (cjN (M9.F 0) (DP 38)) (pw 275 9 (DP 38) 2) &&
    Nat.beq (cjN (M9.F 0) (DP 35)) (pw 275 9 (DP 35) 2) &&
    Nat.beq (cjN (M9.F 1) (DP 34)) (DP 34) &&
    Nat.beq (cjN (M9.F 1) (DP 3)) (pw 275 9 (DP 3) 2) &&
    Nat.beq (cjN (M9.F 1) (DP 38)) (DP 38) &&
    Nat.beq (cjN (M9.F 1) (DP 35)) (pw 275 9 (DP 35) 2) &&
    Nat.beq (cjN (M9.F 2) (DP 3)) (P9 73)) = true := by quickRfl
theorem k9D : allN 81 (fun u => allN 81 fun v => u == v || !Nat.beq (P9 u) (P9 v)) = true := by
  quickRfl

end CertificateChecks.KernelItem434

end
