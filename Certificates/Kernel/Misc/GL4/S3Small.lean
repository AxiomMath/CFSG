module

public import Certificates.Kernel.Misc.GL4.S3Data
public import Certificates.Data.Kernel.Misc.GL4Grp
public import Certificates.Data.S3x3GL42

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.GL4S3

open Matrix CFSG.KC.Misc.GL4 Certificates.A5GL42 Certificates.S3x3GL42

@[expose] def Irr3C (a b c : Nat) : Prop :=
  ∀ s ∈ subspaceCodes, StabC a s → StabC b s → StabC c s → s = [0] ∨ s = List.range 16

noncomputable instance (a b c : Nat) : Decidable (Irr3C a b c) := by
  unfold Irr3C; infer_instance

theorem stdC : ofCode (sA0 0) = aI ∧ ofCode (sB0 0) = bI ∧ ofCode (sA0 1) = aII ∧
    ofCode (sB0 1) = bII := by
  decide +kernel

theorem centS_ok : centS 0 = true ∧ centS 1 = true := by decide +kernel

theorem typeI_ok : ∀ i < 3, TypeIFacts aI bI (ofCode (cL 0 i)) := by decide +kernel

theorem fpf_ok : (∀ v : Vec4, aII *ᵥ v = v → v = 0) ∧ (∀ v : Vec4, bII *ᵥ v = v → v = 0) := by
  decide +kernel

theorem irr_ok : ∀ i < 3, Irr3C (sA0 1) (sB0 1) (cL 1 i) := by decide +kernel

end CertificateChecks.KernelMisc.GL4S3

end
