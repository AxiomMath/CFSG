
module

public import Certificates.Kernel.Sporadic.ONPrim.Facts
public import Certificates.Kernel.Sporadic.ONNQ.Final
public import CFSG.Quasithin.Recognition.CertPermSimple
public import CFSG.Sporadic.ONOddCore.PrimPt
public import CFSG.Sporadic.Schreier.ONSchreierData

public section

namespace CertificateChecks.KernelSpor.ONPrim

open CFSG.KS.ONPrim CertificateChecks.KernelSpor.ONNQ CFSG.ONSchreier
  CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

set_option maxRecDepth 400000

@[expose] noncomputable def lab (y : Fin nL) : ℕ := labOf (ONPr.R y)

theorem rep_eq {i : ℕ} (hi : i < 5) : repOf i = (CFSG.Sporadic.ONOddCore.primPt hi : ℕ) := by
  rw [repOf_eq i hi]
  rfl

theorem lab_lt (y : Fin nL) : lab y < 5 := (pr_sound.1 y y.isLt).1

theorem lab_primPt {i : ℕ} (hi : i < 5) : lab (CFSG.Sporadic.ONOddCore.primPt hi) = i := by
  have h := (pr_sound.2.2.2.2 i hi).2
  rw [rep_eq hi] at h
  exact h

theorem card_lab {i : ℕ} (hi : i < 5) :
    (Finset.univ.filter fun y : Fin nL => lab y = i).card = primSizes.getD i 0 := by
  refine Eq.trans ?_ (pr_sound.2.2.2.1 i hi)
  apply Finset.card_bij (fun (a : Fin nL) _ => (a : ℕ))
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_range.2 a.isLt, ha.2⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb
    exact ⟨⟨b, hb.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hb.2⟩, rfl⟩

section Group

theorem lineRegs_one_nq : lineRegs 1 = nqRho h1Word := by
  have e : ptoLetters 2 h1Word = [((1 : Fin 2), false), ((0 : Fin 2), true), ((1 : Fin 2), true)] := by
    decide
  rw [CFSG.Sporadic.ONOddCore.lineRegs_one, nqRho, nqEv2, e]
  simp only [Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_cons_false,
    Quiver.SchreierGraph.evalWord_nil, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false]
  group

theorem lineRegs_two_nq : lineRegs 2 = nqRho h2Word := by
  have e : ptoLetters 2 h2Word = [((1 : Fin 2), false), ((1 : Fin 2), false), ((0 : Fin 2), false),
      ((1 : Fin 2), false), ((1 : Fin 2), false), ((0 : Fin 2), false), ((1 : Fin 2), true),
      ((0 : Fin 2), true), ((1 : Fin 2), true), ((1 : Fin 2), true), ((0 : Fin 2), true),
      ((1 : Fin 2), true), ((1 : Fin 2), true)] := by
    decide
  rw [CFSG.Sporadic.ONOddCore.lineRegs_two, nqRho, nqEv2, e]
  simp only [Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_cons_false,
    Quiver.SchreierGraph.evalWord_nil, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false]
  group

theorem TT_two (x : Fin nL) : TT 2 x = (lineRegs 1 x : ℕ) := by
  have e := TT_eq (h := 2) (by norm_num) x
  rw [nqP_two, ← lineRegs_one_nq] at e
  exact e

theorem TT_three (x : Fin nL) : TT 3 x = (lineRegs 2 x : ℕ) := by
  have e := TT_eq (h := 3) (by norm_num) x
  rw [nqP_three, ← lineRegs_two_nq] at e
  exact e

theorem TT_gen {k : ℕ} (hk : k < 2) (x : Fin nL) : TT (2 + k) x = (lineRegs (1 + k) x : ℕ) := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · exact TT_two x
  · exact TT_three x

theorem gen_mem {k : ℕ} (hk : k < 2) : lineRegs (1 + k) ∈ lineSubgroup := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem lab_gen {k : ℕ} (hk : k < 2) (x : Fin nL) : lab (lineRegs (1 + k) x) = lab x := by
  unfold lab
  rw [← TT_gen hk]
  exact pr_sound.2.1 (2 + k) (by omega) x x.isLt

theorem lab_inv : ∀ h ∈ lineSubgroup, ∀ x, lab (h x) = lab x := by
  intro h hh
  rw [lineSubgroup] at hh
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact lab_gen (k := 0) (by norm_num)
    · exact lab_gen (k := 1) (by norm_num)
  | one => exact fun _ => rfl
  | mul g h _ _ hg hh => exact fun x => by rw [Equiv.Perm.mul_apply, hg, hh]
  | inv g _ hg => exact fun x => by rw [← hg (g⁻¹ x)]; simp

theorem foldr_mem (z : Fin nL) : ∀ ks : List ℕ, (∀ k ∈ ks, k < 2) →
    ∃ g ∈ lineSubgroup, (g z : ℕ) = ks.foldr (fun k w => TT (2 + k) w) (z : ℕ)
  | [], _ => ⟨1, one_mem _, rfl⟩
  | k :: ks, hks => by
    obtain ⟨g, hg, e⟩ := foldr_mem z ks fun j hj => hks j (List.mem_cons_of_mem _ hj)
    have hk := hks k List.mem_cons_self
    refine ⟨lineRegs (1 + k) * g, mul_mem (gen_mem hk) hg, ?_⟩
    rw [List.foldr_cons, ← e, Equiv.Perm.mul_apply, TT_gen hk]

theorem mem_orbit_iff_lab {i : ℕ} (hi : i < 5) (y : Fin nL) :
    y ∈ MulAction.orbit lineSubgroup (CFSG.Sporadic.ONOddCore.primPt hi) ↔ lab y = i := by
  constructor
  · rintro ⟨g, rfl⟩
    change lab ((g : Equiv.Perm (Fin nL)) (CFSG.Sporadic.ONOddCore.primPt hi)) = i
    rw [lab_inv _ g.2, lab_primPt]
  · intro h
    obtain ⟨ks, hks, e⟩ := (pr_sound.2.2.1 y y.isLt)
    have h' : labOf (ONPr.R y) = i := h
    rw [h', rep_eq hi] at e
    obtain ⟨g, hg, e'⟩ := foldr_mem (CFSG.Sporadic.ONOddCore.primPt hi) ks hks
    exact ⟨⟨g, hg⟩, Fin.ext (e'.trans e.symm)⟩

theorem fix_zero : ∀ h ∈ lineSubgroup, h (0 : Fin nL) = 0 := by
  intro h hh
  rw [lineSubgroup] at hh
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · apply Fin.ext
      rw [← TT_two]
      exact pr_head.1
    · apply Fin.ext
      rw [← TT_three]
      exact pr_head.2
  | one => rfl
  | mul g h _ _ hg hh => rw [Equiv.Perm.mul_apply, hh, hg]
  | inv g _ hg => rw [Equiv.Perm.inv_eq_iff_eq, hg]

theorem card_orbit {i : ℕ} (hi : i < 5) :
    Nat.card (MulAction.orbit lineSubgroup (CFSG.Sporadic.ONOddCore.primPt hi)) =
      CFSG.Sporadic.ONOddCore.primSizes.getD i 0 := by
  have hs : MulAction.orbit lineSubgroup (CFSG.Sporadic.ONOddCore.primPt hi) =
      ↑(Finset.univ.filter fun y : Fin nL => lab y = i) := by
    ext y
    rw [mem_orbit_iff_lab, Finset.coe_filter]
    simp
  rw [hs, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_lab hi]
  rfl

theorem le_orbit {i : ℕ} (hi : i < 5) {y : Fin nL}
    (hy : y ∈ MulAction.orbit lineSubgroup (CFSG.Sporadic.ONOddCore.primPt hi)) :
    (CFSG.Sporadic.ONOddCore.primPt hi : ℕ) ≤ y := by
  have h : labOf (ONPr.R y) = i := (mem_orbit_iff_lab hi y).1 hy
  have hle := (pr_sound.1 y y.isLt).2
  rw [h, rep_eq hi] at hle
  exact hle

theorem cover (y : Fin nL) :
    ∃ i, ∃ hi : i < 5, y ∈ MulAction.orbit lineSubgroup (CFSG.Sporadic.ONOddCore.primPt hi) :=
  ⟨lab y, lab_lt y, (mem_orbit_iff_lab (lab_lt y) y).2 rfl⟩

theorem sizes_div : ∀ S : Finset (Fin 5), (0 : Fin 5) ∈ S →
    (∑ i ∈ S, primSizes.getD i 0) ∣ 122760 → S = {0} ∨ S = Finset.univ := by
  decide +kernel

theorem preprim : MulAction.IsPreprimitive Pl (Fin nL) := by
  classical
  let lab' : Fin nL → Fin 5 := fun y => ⟨lab y, lab_lt y⟩
  have hcard : ∀ i : Fin 5, (Finset.univ.filter fun p => lab' p = i).card = primSizes.getD i 0 :=
    fun i => by
      rw [← card_lab i.isLt]
      congr 1
  have h0 : lab' 0 = 0 := Fin.ext (lab_primPt (i := 0) (by norm_num))
  refine CFSG.Quasithin.isPreprimitive_of_suborbit_labels' (0 : Fin nL)
    (lineSubgroup.subgroupOf Pl) ?_ lab' ?_ ?_
  · intro h hh
    exact fix_zero h.1 (Subgroup.mem_subgroupOf.1 hh)
  · intro p q hpq
    have hq : lab q = lab p := (congrArg Fin.val hpq).symm
    obtain ⟨g1, e1⟩ := (mem_orbit_iff_lab (lab_lt p) p).2 rfl
    obtain ⟨g2, e2⟩ := (mem_orbit_iff_lab (lab_lt p) q).2 hq
    refine ⟨⟨(g2 * g1⁻¹ : lineSubgroup), lineSubgroup_le (g2 * g1⁻¹).2⟩,
      Subgroup.mem_subgroupOf.2 (g2 * g1⁻¹).2, ?_⟩
    rw [← e1, ← e2]
    change ((g2 * g1⁻¹ : lineSubgroup) : Equiv.Perm (Fin nL)) ((g1 : Equiv.Perm (Fin nL)) _) =
      (g2 : Equiv.Perm (Fin nL)) _
    simp
  · intro S hS hd
    rw [Fintype.card_fin, Finset.sum_congr rfl fun i _ => hcard i] at hd
    rw [h0] at hS ⊢
    exact sizes_div S hS hd

theorem prim_cert :
    (∀ h ∈ lineSubgroup, h 0 = 0) ∧
      (∀ i (hi : i < 5), Nat.card (MulAction.orbit lineSubgroup (CFSG.Sporadic.ONOddCore.primPt hi)) =
        CFSG.Sporadic.ONOddCore.primSizes.getD i 0 ∧
          ∀ y ∈ MulAction.orbit lineSubgroup (CFSG.Sporadic.ONOddCore.primPt hi),
            (CFSG.Sporadic.ONOddCore.primPt hi : ℕ) ≤ y) ∧
      (∀ y : Fin nL, ∃ i, ∃ hi : i < 5,
        y ∈ MulAction.orbit lineSubgroup (CFSG.Sporadic.ONOddCore.primPt hi)) ∧
      MulAction.IsPreprimitive Pl (Fin nL) :=
  ⟨fix_zero, fun _ hi => ⟨card_orbit hi, fun _ hy => le_orbit hi hy⟩, cover, preprim⟩

end Group

end CertificateChecks.KernelSpor.ONPrim

end
