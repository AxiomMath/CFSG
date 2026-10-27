
module

public import Certificates.Kernel.IdxFour.OrbitOK
public import CFSG.Certificates.Kernel.IdxFourOrbitTreeSound
public import CFSG.GF2Type.Smith1979.IdxFourModelOrbitBase
public import Certificates.Certificate17600

public section

namespace CFSG.KD.IF4O

open CFSG.KC.IF4C CFSG.KC.IF4O CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.IdxFour

theorem rows_gens : rowsP (look G 0) = a3Rows ∧ rowsP (look G 1) = a5Rows ∧
    rowsP (look G 2) = y3Rows := by
  decide +kernel

theorem exists_E0_gen : ∀ g < 3, ∃ U ∈ E0, IsP U (look G g) :=
  exists_E0_of_rows rows_gens.1 rows_gens.2.1 rows_gens.2.2

theorem exists_E0_378 (v : V12) (hv : inO378 v) : ∃ U ∈ E0, U (vecOf 3) = v :=
  exists_E0_of_inO378b cf17603tree exists_E0_gen v hv

theorem exists_E0_1701 (v : V12) (hv : inO1701 v) : ∃ U ∈ E0, U (vecOf 15) = v :=
  exists_E0_of_inO1701b cf17603tree exists_E0_gen v hv

theorem M0_mem_sing {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ M0) {x : V12}
    (hx : inO378 x ∨ inO1701 x) : inO378 (g x) ∨ inO1701 (g x) := by
  have h0 : x ≠ 0 ∧ q0 x = 0 := hx.elim ne_zero_of_inO378 ne_zero_of_inO1701
  refine (singular_cases ((LinearEquiv.map_ne_zero_iff g).2 h0.1) ?_).1
  rw [(M0_le_gammaU hg).1 x, h0.2]

theorem not_inO1701 {x : V12} (h : inO378 x) : ¬inO1701 x := fun h' =>
  (singular_cases (ne_zero_of_inO378 h).1 (ne_zero_of_inO378 h).2).2 ⟨h, h'⟩

theorem ncard_sing : {x : V12 | inO378 x ∨ inO1701 x}.ncard = 2079 := by
  rw [Set.setOf_or, Set.ncard_union_eq (s := {a | inO378 a}) (t := {a | inO1701 a})
      (Set.disjoint_left.2 fun _ h1 h2 => not_inO1701 h1 h2),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  change Nat.card {v : V12 // inO378 v} + Nat.card {v : V12 // inO1701 v} = 2079
  rw [card_inO378, card_inO1701]

theorem M0_inv_378 {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ M0) {v : V12} (hv : inO378 v) :
    inO378 (U v) := by
  by_contra hne
  have h1701 : inO1701 (U v) := (M0_mem_sing hU (Or.inl hv)).resolve_left hne
  have hw : inO378 (vecOf 3) := by
    change Orb.inO378b (codeOf (vecOf 3)) = true
    rw [codeOf_vecOf (by norm_num)]
    decide +kernel
  obtain ⟨E1, hE1, hE1w⟩ := exists_E0_378 v hv
  obtain ⟨E3, hE3, h3⟩ := exists_E0_1701 (U v) h1701
  have horb : MulAction.orbit M0 (vecOf 3) = {x | inO378 x ∨ inO1701 x} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact M0_mem_sing g.2 (Or.inl hw)
    · rintro (hx | hx)
      · obtain ⟨E, hE, hEx⟩ := exists_E0_378 x hx
        exact ⟨⟨E, E0_le_M0 hE⟩, hEx⟩
      · obtain ⟨E2, hE2, h2⟩ := exists_E0_1701 x hx
        refine ⟨⟨E2 * E3⁻¹ * U * E1, mul_mem (mul_mem (mul_mem (E0_le_M0 hE2)
          (inv_mem (E0_le_M0 hE3))) hU) (E0_le_M0 hE1)⟩, ?_⟩
        change (E2 * E3⁻¹ * U * E1) (vecOf 3) = x
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hE1w, ← h3,
          inv_apply_apply, h2]
  have hdvd := Subgroup.index_dvd_card (MulAction.stabilizer M0 (vecOf 3))
  rw [MulAction.index_stabilizer, horb, ncard_sing, Certificates.certificate17600] at hdvd
  norm_num at hdvd

theorem M0_inv_1701 {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ M0) {v : V12} (hv : inO1701 v) :
    inO1701 (U v) := by
  refine (M0_mem_sing hU (Or.inr hv)).resolve_left fun h => ?_
  have := M0_inv_378 (inv_mem hU) h
  rw [inv_apply_apply] at this
  exact not_inO1701 this hv

theorem orbit_facts :
    (∀ U ∈ M0, ∀ v : V12, Orb.inO378b (codeOf v) = true → Orb.inO378b (codeOf (U v)) = true) ∧
    (∀ U ∈ M0, ∀ v : V12, Orb.inO1701b (codeOf v) = true →
      Orb.inO1701b (codeOf (U v)) = true) ∧
    (∀ v : V12, Orb.inO378b (codeOf v) = true → ∃ U ∈ E0, U (vecOf 3) = v) ∧
    (∀ v : V12, Orb.inO1701b (codeOf v) = true → ∃ U ∈ E0, U (vecOf 15) = v) :=
  ⟨fun _ hU _ hv => M0_inv_378 hU hv, fun _ hU _ hv => M0_inv_1701 hU hv, exists_E0_378,
    exists_E0_1701⟩

end CFSG.KD.IF4O

end
