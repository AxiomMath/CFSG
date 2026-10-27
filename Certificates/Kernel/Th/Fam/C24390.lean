module

public import Certificates.Kernel.Th.Fam.K
public import CFSG.Sporadic.Recognition.ThMultiplierInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Th.Max3.Relations

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Max3.AllConj CFSG.Sporadic.Recognition.ThMultiplier

@[expose] def vT (j : Fin 5) : TE := .nfE (vS j) (vE j)

@[expose] def iotaT (c : Fin 5 → ℕ) : TE := .prodFn 5 fun j => .pow (vT j) (c j)

@[expose] def mA1T : TE := .mul (.pow .y 5) .x
@[expose] def mA2T : TE := .mul (.mul .y .x) (.pow .y 5)
@[expose] def mA3T : TE :=
  .mul (.mul (.ab gWord) (.pow (.mul .a (.mul (.mul (.ab (invWord gWord)) (.q 0)) (.ab gWord))) 9))
    (.pow .y 4)

@[expose] def bitsN (m : ℕ) : Fin 5 → ℕ := fun j => m / 2 ^ j.val % 2

theorem ok24390a : (List.finRange 5).all (fun j =>
    Nat.beq ((TE.mul (vT j) (vT j)).pk thK) (TE.one.pk thK)) = true := by quickRfl

theorem ok24390b : (List.finRange 5).all (fun i => (List.finRange 5).all fun j =>
    Nat.beq ((TE.mul (vT i) (vT j)).pk thK) ((TE.mul (vT j) (vT i)).pk thK)) = true := by
  quickRfl

theorem ok24390c : (List.range 32).all (fun m => Nat.beq m 0 ||
    CFSG.KC.Th.BigS.notB (Nat.beq ((iotaT (bitsN m)).pk thK) (TE.one.pk thK))) = true := by
  quickRfl

theorem ok24390d : (List.finRange 5).all (fun j =>
    Nat.beq ((TE.mul mA1T (vT j)).pk thK) ((TE.mul (iotaT (colA1 j)) mA1T).pk thK) &&
    Nat.beq ((TE.mul mA2T (vT j)).pk thK) ((TE.mul (iotaT (colA2 j)) mA2T).pk thK) &&
    Nat.beq ((TE.mul mA3T (vT j)).pk thK) ((TE.mul (iotaT (colA3 j)) mA3T).pk thK)) = true := by
  quickRfl

end CertificateChecks.KernelTh.Fam

end
