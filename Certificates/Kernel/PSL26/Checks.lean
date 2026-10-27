module

public import Certificates.Kernel.PSL26.Chain
public import Certificates.Data.Kernel.B3S3K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPSL26

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K (cm pw)
open CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier

@[expose] noncomputable def idP : ℕ := pidn 26 5

@[expose] noncomputable def ivP (p : ℕ) : ℕ := pinvS 26 5 (mask 5) p

@[expose] noncomputable def trP (i k : ℕ) : ℕ := P26.TR (Nat.add (roff 26 (26 * 5) (P26.LR i)) k)

@[expose] noncomputable def rgP (P : ℕ) : Bool :=
  permB 26 5 P && allN 26 (fun p => Nat.blt (pg 5 (mask 5) P p) 26)

@[expose] noncomputable def trOK : Bool :=
  allN 26 (fun k => rgP (trP 0 k)) && allN 25 (fun k => rgP (trP 1 k)) &&
    allN 12 (fun k => rgP (trP 2 k))

@[expose] noncomputable def ordG (g : ℕ) : Bool :=
  Nat.beq (pw 26 5 g 12) idP || Nat.beq (pw 26 5 g 13) idP || Nat.beq (pw 26 5 g 5) idP

@[expose] noncomputable def ordK (a b c : ℕ) : Bool :=
  ordG (cm 26 5 (cm 26 5 (trP 0 a) (trP 1 b)) (trP 2 c))

@[expose] noncomputable def ordRow (a : ℕ) : Bool := allN 25 fun b => allN 12 fun c => ordK a b c

@[expose] noncomputable def clK (A o : ℕ) : Bool :=
  allN 26 fun i => Nat.blt (DW (o + i)) 26 && Nat.beq (PD (DW (o + i))) (cm 26 5 A (PD i))

theorem c7044W : szOK 26 5 = true := by quickRfl

theorem c7044BP : allN 3 (fun t => Nat.beq (ruBaseArr 26 [0, 1, 2])[t]!
    (pg 5 (mask 5) P26.BP t)) = true := by quickRfl

theorem c7044P : allN 9 (fun j => permOK 26 5 (mask 5) (26 * 5) (P26.S j) (P26.SI j)) = true := by
  quickRfl

theorem c7044PB : allN 9 (fun j => permB 26 5 (P26.S j)) = true := by quickRfl

theorem c7044C : Nat.beq (rcnt (P26.LR 0)) 26 = true ∧ Nat.beq (rcnt (P26.LR 1)) 25 = true ∧
    Nat.beq (rcnt (P26.LR 2)) 12 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem c7044DP : allN 26 (fun k => permB 26 5 (PD k)) = true := by quickRfl

theorem c7044T : trOK = true := by quickRfl

theorem c7044O0 : allN 7 (fun a => ordRow a) = true := by quickRfl
theorem c7044O1 : allN 7 (fun a => ordRow (Nat.add 7 a)) = true := by quickRfl
theorem c7044O2 : allN 6 (fun a => ordRow (Nat.add 14 a)) = true := by quickRfl
theorem c7044O3 : allN 6 (fun a => ordRow (Nat.add 20 a)) = true := by quickRfl

theorem c7044L : clK (P26.S 0) 0 = true ∧ clK (P26.S 1) 26 = true ∧
    clK (ivP (P26.S 0)) 52 = true ∧ clK (ivP (P26.S 1)) 78 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem c7044A : allN 26 (fun k => !Nat.beq (PD k) (P26.S 2)) = true ∧ Nat.beq (PD 0) idP = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem c7044R : (Nat.beq (pw 26 5 (P26.S 0) 13) idP && !Nat.beq (P26.S 0) idP &&
    Nat.beq (pw 26 5 (P26.S 1) 2) idP && !Nat.beq (P26.S 1) idP &&
    Nat.beq (pw 26 5 (P26.S 2) 2) idP && !Nat.beq (P26.S 2) idP &&
    Nat.beq (cm 26 5 (cm 26 5 (cm 26 5 (P26.S 1) (P26.S 0)) (P26.S 1)) (P26.S 0)) idP &&
    Nat.beq (cm 26 5 (P26.S 2) (P26.S 1)) (cm 26 5 (P26.S 1) (P26.S 2))) = true := by
  quickRfl

theorem c7044N1 : Nat.beq (pw 26 5 (cm 26 5 (cm 26 5 (trP 0 1) (trP 1 0)) (trP 2 0)) 5) idP =
    false := by
  decide +kernel

theorem c7044N2 : Nat.beq (rcnt (P26.LR 1)) 26 = false := by decide +kernel

theorem c7044N3 : clK (P26.S 2) 0 = false := by decide +kernel

theorem c7044N4 : Nat.beq (pw 26 5 (P26.S 0) 2) idP = false := by decide +kernel

end CertificateChecks.KernelPSL26

end
