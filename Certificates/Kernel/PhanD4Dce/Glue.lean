module

public import Certificates.Kernel.PhanD4Dce.ChainGlue
public import Certificates.Kernel.PhanB3.Glue

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan.Q3G CFSG.KC.MiscCoset
  CFSG.Certificates.CosetEnumeration

theorem card_le_of_index
    (hidx : phanR.FiniteIndex ∧ phanR.index ≤ 1516320) :
    Finite PhanD4Group ∧ Nat.card PhanD4Group ≤ 4 * 4952179814400 := by
  have : Finite PhanA3Group := card_phanA3Group_le.1
  have hfinH : Finite phanR := by
    rw [← range_a3Hom]
    exact Finite.of_surjective _ a3Hom.rangeRestrict_surjective
  have := hidx.1
  have : Finite (PhanD4Group ⧸ phanR) := Subgroup.finite_quotient_of_finiteIndex
  have hfin : Finite PhanD4Group := Finite.of_subgroup_quotient phanR
  refine ⟨hfin, ?_⟩
  rw [← phanR.index_mul_card]
  calc phanR.index * Nat.card phanR ≤ 1516320 * 13063680 :=
        Nat.mul_le_mul hidx.2 card_phanR_le
    _ = 4 * 4952179814400 := by norm_num

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan.Q3G in
theorem certificate270006_of
    (hidx : phanR.FiniteIndex ∧ phanR.index ≤ 1516320) :
    (Finite PhanD4Group ∧ Nat.card PhanD4Group ≤ 4 * 4952179814400) ∧
      (∃ N : Subgroup PhanD4Group, N.Normal ∧ Nat.card N ≤ 4 ∧
        (∀ w ∈ d4CtRels, wordVal ctEltP w ∈ N) ∧
        ∀ i : Fin 8,
          (wordVal ctEltP (decodeWord 8 phanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ N) ∧
      (Finite (PG 4 sl3Rels) ∧ Nat.card (PG 4 sl3Rels) ≤ 5616) := by
  obtain ⟨hfin, hle⟩ := card_le_of_index hidx
  exact ⟨⟨hfin, hle⟩, ker_facts hle, CertificateChecks.KernelPhanB3.card_sl3⟩

end CFSG.KD.PhanD4Dce

end
