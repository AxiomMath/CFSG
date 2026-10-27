module

public import Certificates.Data.Kernel.SlpRel
public import Certificates.Kernel.Fi22Core.Data
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22CoverCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSlpRel

open CFSG.F3.Native CFSG.KC.Enum CFSG.KC.SlpRel CertificateChecks.KernelFi22C
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

@[expose] noncomputable def frcV (x : V) (k : V → Bool) : Bool :=
  strictB x.p fun p => strictB x.m fun m => k ⟨p, m⟩

@[expose] noncomputable def fi22NZ (X : V) : Bool := Nat.beq (Nat.land X.p (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def fi22SlpK (prog : List (List Nat)) (ps : List (List Nat × List Nat))
    (ne : List Nat) : Bool :=
  strictB SP fun sp => frcV LA fun a => frcV LB fun b => frcV LI fun one =>
    slpRelK frcV (CFSG.KS.F3L.mulLane (nat_lit 77) sp) one eqF fi22NZ [a, b] prog ps ne

set_option Elab.async false

theorem ch129040_ok : fi22SlpK fi22HeisProg fi22HeisRels [fi22HeisZ] = true := by
  quickRfl

theorem ch129041_ok : fi22SlpK fi22CoverProg fi22CoverRels [41] = true := by
  quickRfl

end CertificateChecks.KernelSlpRel

end
