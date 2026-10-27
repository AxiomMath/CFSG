
module

public import Certificates.Kernel.J4Count.PrimBase

public import Certificates.Kernel.J4Count.PrimData
public import Certificates.Kernel.J4Count.FixCEElt
public import Certificates.Kernel.J4Count.HOrder
public import Certificates.Kernel.J4Hub.Card
public import CFSG.Sporadic.J4.Simple
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Prim

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT MulAction
open CFSG.Sporadic.J4Schreier (H v rootBits)
open CFSG.KD.J4Prim
open CFSG.KC.J4Q (vecJ)
open CFSG.KD.J4Q (rm Ai Bi)
open CertificateChecks.KernelJ4Count.FixCE (PR PR_of inv_smul_PR)
open CertificateChecks.KernelJ4Count (ncard_orbit_mem mem_orbit_of_ncard qv qv_mem exists_sz sz_zero
  qv_zero L7 stabilizer_v_eq_Hj' stabilizer_v H_eq_Hj' card_Hj')
open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply toVecD_xor toVecD_zero)
open scoped Matrix

noncomputable def lab (p : X) : Fin 7 :=
  Classical.choose ((L7_iff _).1 (ncard_orbit_mem p.2))

theorem stabilizer_x0 : stabilizer J x0 = Hj := by
  rw [← stabilizer_v_eq_Hj']
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff]
  rfl

theorem card_X : Nat.card X = 173067389 := by
  have h1 := Subgroup.card_mul_index (stabilizer J v)
  rw [index_stabilizer, stabilizer_v_eq_Hj', card_Hj', CertificateChecks.KernelJ4Hub.card_J'] at h1
  rw [Nat.card_coe_set_eq]
  omega

theorem lab_spec (p : X) : subSizesF (lab p) = (orbit H (p : Row)).ncard :=
  Classical.choose_spec ((L7_iff _).1 (ncard_orbit_mem p.2))

theorem lab_eq_iff (p : X) (i : Fin 7) : lab p = i ↔ (orbit H (p : Row)).ncard = subSizesF i := by
  rw [← lab_spec]
  exact ⟨fun h => by rw [h], fun h => subSizesF_inj h⟩

theorem lab_orb (p q : X) (h : lab p = lab q) : ∃ g ∈ Hj, g • p = q := by
  have hpq : (orbit H (q : Row)).ncard = (orbit H (p : Row)).ncard := by
    rw [← lab_spec, ← lab_spec, h]
  obtain ⟨⟨g, hg⟩, e⟩ := mem_orbit_of_ncard p.2 q.2 hpq
  refine ⟨g, H_eq_Hj' ▸ hg, Subtype.ext ?_⟩
  exact e

theorem lab_x0 : lab x0 = 0 := by
  rw [lab_eq_iff]
  have h := sz_zero
  change (orbit H (qv 0)).ncard = 1 at h
  rw [qv_zero] at h
  exact h

theorem card_lab (i : Fin 7) :
    (Finset.univ.filter (fun p : X => lab p = i)).card = subSizesF i := by
  classical
  obtain ⟨l, hl, hsz⟩ := exists_sz ((L7_iff _).2 ⟨i, rfl⟩)
  have hset : ∀ p : X, lab p = i ↔ (p : Row) ∈ orbit H (qv l) := by
    intro p
    rw [lab_eq_iff]
    constructor
    · intro hp
      exact mem_orbit_of_ncard (qv_mem hl) p.2 (hp.trans hsz.symm)
    · intro hp
      rw [← hsz]
      exact congrArg Set.ncard (orbit_eq_iff.2 hp)
  have hsub : orbit H (qv l) ⊆ orbit J v := by
    rintro w ⟨⟨g, -⟩, rfl⟩
    obtain ⟨k, hk⟩ := qv_mem hl
    change k • v = qv l at hk
    refine ⟨g * k, ?_⟩
    change (g * k) • v = g • qv l
    rw [mul_smul, hk]
  have e : (Finset.univ.filter (fun p : X => lab p = i)).map (Function.Embedding.subtype _) =
      (Set.toFinite (orbit H (qv l))).toFinset := by
    ext w
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.subtype_apply, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hset p).1 hp
    · intro hw
      exact ⟨⟨w, hsub hw⟩, (hset _).2 hw, rfl⟩
  rw [← Finset.card_map, e, ← Set.ncard_eq_toFinset_card _]
  exact hsz

instance : Nontrivial X := by
  rw [← Finite.one_lt_card_iff_nontrivial, card_X]
  norm_num

theorem isPreprimitive_X : IsPreprimitive J X := by
  classical
  refine isPreprimitive_of_labels x0 Hj (fun h hh => by
      have : h ∈ stabilizer J x0 := by rw [stabilizer_x0]; exact hh
      exact this) lab lab_orb fun S hS hdvd => ?_
  rw [lab_x0] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : X => lab p = i)).card) =
      ∑ i ∈ S, subSizesF i := Finset.sum_congr rfl fun i _ => card_lab i
  rw [hsum, ← Nat.card_eq_fintype_card, card_X] at hdvd
  exact subSizesF_blocks S hS hdvd

theorem isCoatom_Hj' : IsCoatom Hj := by
  have := isPreprimitive_X
  rw [← stabilizer_x0]
  exact (isCoatom_stabilizer_iff_preprimitive J x0).2 this

theorem isSimpleGroup_J' : IsSimpleGroup J := by
  have := finite_J
  have := isPreprimitive_X
  refine isSimpleGroup_of_conj_product (Ω := X) ?_ a b cJ closure_ab x0
    (ab_pow' CertificateChecks.KernelJ4Q.matFacts) (z_pow' CertificateChecks.KernelJ4Q.matFacts)
    ?_ ?_
  · rw [card_X]
    norm_num
  · rw [stabilizer_x0, card_Hj']
    norm_num
  · rw [stabilizer_x0, card_Hj']
    norm_num

end CertificateChecks.KernelJ4Count.Prim

end
