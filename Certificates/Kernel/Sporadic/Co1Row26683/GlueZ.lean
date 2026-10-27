module

public import Certificates.Kernel.Sporadic.Co1Row26683.ChecksZ
public import CFSG.Sporadic.Co1Block.TwoBTri

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co1Row26683

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.KC.Co1T CFSG.KS.Raw.Orb
  CertificateChecks.KernelCo1B.Tri2045 CertificateChecks.KernelSpor

theorem triZK_sound {Z PT P : Nat} (h : CFSG.KS.Co1Row26683Z.triZK Z PT P = true) :
    (∀ k < 1365, triOneK (CFSG.KC.Co1F2.trK 24 Z) PT P k = true) ∧
      CFSG.KC.Enum.invoOK 1365 11 (CFSG.KS.mask 11) 15015 P = true := by
  unfold CFSG.KS.Co1Row26683Z.triZK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  refine ⟨fun k hk => ?_, h2⟩
  have := CFSG.KC.Pack.allBlk_spec h1 k hk
  rwa [Nat.add_eq, Nat.zero_add] at this

theorem zeta_parts :
    (∀ k < 1365, triOneK (CFSG.KC.Co1F2.trK 24 (C26683M.Z.M 2)) TB.PT C26683Z.PZ k = true) ∧
      CFSG.KC.Enum.invoOK 1365 11 (CFSG.KS.mask 11) 15015 C26683Z.PZ = true :=
  triZK_sound ch26683Z

theorem prep_zeta {c : C₁}
    (hc : MRep (CFSG.KS.Raw.unpack 24 24 (C26683M.Z.M 2)) ((c : GA) : GL24)) :
    PRep 1365 11 C26683Z.PZ (triHom c) := by
  obtain ⟨hok, hperm⟩ := triOK_of rfl zeta_parts.1
  apply prep_of_rep
  rw [← hperm]
  exact rep_triHom hc hok

end CertificateChecks.KernelSpor.Co1Row26683

end
