module

public import Certificates.Data.Kernel.EvenSporSuz.OuterBlk
public import Certificates.Kernel.EvenSporSuz.Fours25010
import all Certificates.Kernel.EvenSporSuz.Data
import all Init.Data.List.SplitOn.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSuz.OW CFSG.EvenSporadicStandard.TwoSuz.outerWordsText

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.EvenSporadicStandard.TwoSuz

@[expose] noncomputable def owW : List (List ℤ) := (nonEmptyLines OW.chars).map owK

@[expose] noncomputable def B2 : OuterBlock := blockW owW 0 2 2

@[expose] noncomputable def B3 : OuterBlock := blockW owW 10 2 2

@[expose] noncomputable def L1M (b : OuterBlock) : List (List ℕ) :=
  subR l0M l0I b.gens.length fun s => b.gens.getD s []

@[expose] noncomputable def L1I (b : OuterBlock) : List (List ℕ) :=
  subRI l0M l0I b.gens.length fun s => b.gens.getD s []

@[expose] noncomputable def L2M (b : OuterBlock) : List (List ℕ) :=
  subR (L1M b) (L1I b) b.us.length fun j => outerCommW (b.us.getD j []) (b.vs.getD j [])

@[expose] noncomputable def L2I (b : OuterBlock) : List (List ℕ) :=
  subRI (L1M b) (L1I b) b.us.length fun j => outerCommW (b.us.getD j []) (b.vs.getD j [])

@[expose] noncomputable def miscK (b : OuterBlock) : Bool :=
  (b.us.length == b.vs.length) && (b.zs.length == b.gens.length) &&
    b.gens.all (fun w => CFSG.Monster.B.Co2.Native.lettersOK 2 w) &&
    (b.us ++ b.vs).all (CFSG.Monster.B.Co2.Native.lettersOK b.gens.length) &&
    b.zs.all (CFSG.Monster.B.Co2.Native.lettersOK b.us.length) &&
    CFSG.Monster.B.Co2.Native.lettersOK b.gens.length b.neg

@[expose] noncomputable def zsK (b : OuterBlock) : Bool :=
  (List.range b.gens.length).all fun s =>
    evalR (L2M b) (L2I b) ((b.zs.getD s []).map zCode) == (L1M b).getD s oneR

set_option maxHeartbeats 0 in
theorem ch25030M_lines : (nonEmptyLines OW.chars).all owOK = true := by decide +kernel

theorem ch25030M_hdr :
    owW.getD 0 [] = [((2 : ℕ) : ℤ), ((2 : ℕ) : ℤ)] ∧ owW.getD 10 [] = [((2 : ℕ) : ℤ), ((2 : ℕ) : ℤ)] := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch25030M_v2 : validR (L1M B2) (L1I B2) = true ∧ validR (L2M B2) (L2I B2) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch25030M_v3 : validR (L1M B3) (L1I B3) = true ∧ validR (L2M B3) (L2I B3) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch25030M_misc : miscK B2 = true ∧ miscK B3 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ch25030M_z2 : zsK B2 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ch25030M_z3 : zsK B3 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ch25030M_neg : (evalR (L1M B2) (L1I B2) (B2.neg.map zCode) == negR) = true ∧
    (evalR (L1M B3) (L1I B3) (B3.neg.map zCode) == negR) = true := by
  decide +kernel

theorem ch25030Neg_m :
    (evalR (L2M B2) (L2I B2) (B2.neg.map zCode) == negR) = false := by
  decide +kernel

end CertificateChecks.KernelSuz

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSuz

theorem ch25030P_l : B2.gens.all (fun w => lettersK 2 w && cn (W3 w)) = true ∧
    B3.gens.all (fun w => lettersK 2 w && cn (W3 w)) = true := by
  decide +kernel

theorem ch25030P_c2 :
    B2.gens.all (fun w => Nat.beq (pc (W3 w) (SuzTP 2)) (pc (SuzTP 2) (W3 w))) = true := by
  quickRfl

theorem ch25030P_c3 :
    B3.gens.all (fun w => Nat.beq (pc (W3 w) (SuzTP 3)) (pc (SuzTP 3) (W3 w))) = true := by
  quickRfl

theorem ch25030Neg_c :
    B2.gens.all (fun w => Nat.beq (pc (W3 w) (SuzTP 3)) (pc (SuzTP 3) (W3 w))) = false := by
  decide +kernel

end CertificateChecks.KernelSpor.S26990

end
