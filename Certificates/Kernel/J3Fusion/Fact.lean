module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.FusionWords
public import CFSG.Certificates.Kernel.TabMatGrpSound
import Certificates.Kernel.J3Fusion.Check
import all CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Model
import all CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.ModelTuple

public section

namespace CertificateChecks.KernelJ3Fusion

open CFSG.KC.TabMatGrp CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
  CFSG.Sporadic.J3 CFSG.Certificates CertificateChecks.KernelLC.J3Ops CertificateChecks.KernelW4Model

private theorem MatP_A : MatP 80 SA.M = mA Native.j3Data := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound SA.bind, ← SA.eq]
  exact CFSG.Sporadic.SmallF2.rowsMatrix_rowsOfPayload _ _

private theorem MatP_B : MatP 80 SB.M = mB Native.j3Data := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound SB.bind, ← SB.eq]
  exact CFSG.Sporadic.SmallF2.rowsMatrix_rowsOfPayload _ _

private theorem dets : (mA Native.j3Data).det ≠ 0 ∧ (mB Native.j3Data).det ≠ 0 := by
  rw [← MatP_A, ← MatP_B]
  exact seedsK_det rels_ok

private noncomputable abbrev sig : Fin 2 → J3Model := ![a Native.j3Data, b Native.j3Data]

private noncomputable abbrev tau : Fin 7 → J3Model := fun i => segVal sig segs i.val

private theorem hA : MatP 80 SA.M = matOf (J Native.j3Data).subtype (sig 0) := by
  rw [show (sig 0 : J Native.j3Data) = a Native.j3Data from rfl,
    matOf, Subgroup.subtype_apply, coe_a, gA, dif_pos dets.1,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_A]

private theorem hB : MatP 80 SB.M = matOf (J Native.j3Data).subtype (sig 1) := by
  rw [show (sig 1 : J Native.j3Data) = b Native.j3Data from rfl,
    matOf, Subgroup.subtype_apply, coe_b, gB, dif_pos dets.2,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_B]

private theorem uJ_eq (i : Fin 7) : uJ i = segVal sig segs i.val := by
  have hi : i.val < (List.range 7).length := by simp
  unfold uJ uN segVal segs
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  exact prod_pairLetter _ _ _

private theorem letOK_iff {z : ℤ} : letOK z = true ↔ 1 ≤ z.natAbs ∧ z.natAbs ≤ 7 := by
  simp [letOK]

private theorem letG_eq {z : ℤ} (hz : letOK z = true) :
    letG z = if (zL z).2 then tau (zL z).1 else (tau (zL z).1)⁻¹ := by
  rw [letOK_iff] at hz
  unfold letG zL
  by_cases h : 0 < z
  · simp only [if_pos h]
    have hn : (z - 1).toNat < 7 := by omega
    change uN (z - 1).toNat = segVal sig segs ((z - 1).toNat % 7)
    rw [Nat.mod_eq_of_lt hn]
    exact uJ_eq ⟨_, hn⟩
  · simp only [if_neg h]
    have hn : (-z - 1).toNat < 7 := by omega
    change (uN (-z - 1).toNat)⁻¹ = (segVal sig segs ((-z - 1).toNat % 7))⁻¹
    rw [Nat.mod_eq_of_lt hn]
    exact congrArg _ (uJ_eq ⟨_, hn⟩)

private theorem ev_eq : ∀ w : List ℤ, (∀ l ∈ w, letOK l = true) →
    ev w = signedProd tau (w.map zL)
  | [], _ => by rw [ev_nil]; rfl
  | l :: w, h => by
    rw [ev_cons, List.map_cons, signedProd_cons, letG_eq (h l List.mem_cons_self),
      ev_eq w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]

private theorem rel_one {w : List ℤ} (hw : w ∈ invRels ++ clRels ++ clsRels)
    (hl : ∀ l ∈ w, letOK l = true) : ev w = 1 := by
  have hm : (w.map zL, ([] : List (Fin 2 × Bool))) ∈ relPs (invRels ++ clRels ++ clsRels) := by
    unfold relPs
    exact List.mem_map.2 ⟨w, hw, rfl⟩
  have h := grpK_sound Subtype.val_injective hA hB segs (by rfl) _ rels_ok _ hm
  rw [signedProd_nil, mul_one] at h
  rw [ev_eq w hl]
  exact h

private theorem parts : fusPaths.length = 128 ∧ nx.length = 768 ∧ cls.length = 128 ∧
    (∀ q ∈ nx, q < 128) ∧
    (∀ i < 127, cls.getD (i + 1) 0 % 2 = 1 ∨
      (0 < cls.getD (i + 1) 0 / 2 ∧ cls.getD (i + 1) 0 / 2 < 128)) ∧
    fusPaths.getD 0 [] = [] ∧ (∀ p ∈ fusPaths, ∀ j ∈ p, j < 6) ∧
    (∀ g ∈ fusGl, ∀ l ∈ g, letOK l = true) ∧ (∀ c ∈ fusConj, ∀ l ∈ c, letOK l = true) := by
  have h := data_ok
  simp only [dataOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

private theorem getD_ok {L : List (List ℤ)} (h : ∀ g ∈ L, ∀ l ∈ g, letOK l = true) (j : ℕ) :
    ∀ l ∈ L.getD j [], letOK l = true := by
  by_cases hj : j < L.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

private theorem gl_ok (j : ℕ) : ∀ l ∈ fusGl.getD j [], letOK l = true :=
  getD_ok parts.2.2.2.2.2.2.2.1 j

private theorem conj_ok (c : ℕ) : ∀ l ∈ fusConj.getD c [], letOK l = true :=
  getD_ok parts.2.2.2.2.2.2.2.2 c

private theorem pw_ok (i : ℕ) : ∀ l ∈ pw i, letOK l = true := by
  intro l hl
  unfold pw pathWord at hl
  simp only [List.mem_flatten, List.mem_map] at hl
  obtain ⟨_, ⟨j, -, rfl⟩, hl⟩ := hl
  exact gl_ok j l hl

private theorem inv_ok {w : List ℤ} (h : ∀ l ∈ w, letOK l = true) :
    ∀ l ∈ invWordZ w, letOK l = true := fun l hl =>
  letOK_iff.2 (invWordZ_letters (fun l hl => letOK_iff.1 (h l hl)) l hl)

private theorem app_ok {v w : List ℤ} (hv : ∀ l ∈ v, letOK l = true)
    (hw : ∀ l ∈ w, letOK l = true) : ∀ l ∈ v ++ w, letOK l = true := by
  intro l hl
  rcases List.mem_append.1 hl with h | h
  · exact hv l h
  · exact hw l h

private noncomputable abbrev xe (i : ℕ) : J3Model := ev (pw i)

private noncomputable abbrev ge (j : ℕ) : J3Model := ev (fusGl.getD j [])

private theorem xe_zero : xe 0 = 1 := by
  unfold xe pw
  rw [parts.2.2.2.2.2.1]
  exact ev_nil

private theorem ge_inv {j : ℕ} (hj : j < 3) : ge (j + 3) = (ge j)⁻¹ := by
  have hw : fusGl.getD (j + 3) [] ++ fusGl.getD j [] ∈ invRels ++ clRels ++ clsRels :=
    List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
      (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))
  have h := rel_one hw (app_ok (gl_ok _) (gl_ok _))
  rw [ev_append] at h
  exact eq_inv_of_mul_eq_one_left h

private theorem step {i j : ℕ} (hi : i < 128) (hj : j < 6) :
    ∃ q < 128, xe i * ge j = xe q := by
  have hk : 6 * i + j < 768 := by omega
  have hw : clRel (6 * i + j) ∈ invRels ++ clRels ++ clsRels :=
    List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (List.mem_map.2 ⟨6 * i + j, List.mem_range.2 hk, rfl⟩))))
  have hl : ∀ l ∈ clRel (6 * i + j), letOK l = true :=
    app_ok (app_ok (pw_ok _) (gl_ok _)) (inv_ok (pw_ok _))
  have h := rel_one hw hl
  have e1 : (6 * i + j) / 6 = i := by omega
  have e2 : (6 * i + j) % 6 = j := by omega
  unfold clRel at h
  rw [e1, e2, ev_append, ev_append, ev_invWordZ fun l hl => letOK_iff.1 (pw_ok _ l hl)] at h
  refine ⟨nx.getD (6 * i + j) 0, ?_, mul_inv_eq_one.1 h⟩
  have hn : 6 * i + j < nx.length := by rw [parts.2.1]; exact hk
  rw [List.getD_eq_getElem _ _ hn]
  exact parts.2.2.2.1 _ (List.getElem_mem hn)

private theorem xe_inj {i j : ℕ} (hi : i < 128) (hj : j < 128) (h : xe i = xe j) : i = j := by
  by_contra hij
  have hl : pathSegs.length = 128 := by simp [pathSegs]
  have hd := distK_sound hA hB segs (by rfl) pathSegs dist_ok i (by omega) j (by omega) hij
  apply hd
  have ei : pathSegs[i]'(by omega) = (pw i).map zL := by simp [pathSegs]
  have ej : pathSegs[j]'(by omega) = (pw j).map zL := by simp [pathSegs]
  rw [ei, ej, ← ev_eq _ (pw_ok i), ← ev_eq _ (pw_ok j)]
  exact h

private noncomputable abbrev S : Subgroup J3Model :=
  Subgroup.closure (Set.range fun j : Fin 3 => ev (fusGl.getD j []))

private theorem ge_mem {j : ℕ} (hj : j < 6) : ge j ∈ S := by
  by_cases h : j < 3
  · exact Subgroup.subset_closure ⟨⟨j, h⟩, rfl⟩
  · have e : j = (j - 3) + 3 := by omega
    rw [e, ge_inv (by omega)]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨j - 3, by omega⟩, rfl⟩)

private theorem xe_mem (i : ℕ) : xe i ∈ S := by
  unfold xe pw
  rw [ev_pathWord]
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  have hp : ∀ j ∈ fusPaths.getD i [], j < 6 := by
    intro j hj
    by_cases hi : i < fusPaths.length
    · rw [List.getD_eq_getElem _ _ hi] at hj
      exact parts.2.2.2.2.2.2.1 _ (List.getElem_mem hi) j hj
    · rw [List.getD_eq_default _ _ (by omega)] at hj
      simp at hj
  exact ge_mem (hp j hj)

private theorem mem_S_iff {y : J3Model} : y ∈ S ↔ ∃ i < 128, xe i = y := by
  constructor
  · intro hy
    induction hy using Subgroup.closure_induction_right with
    | one => exact ⟨0, by omega, xe_zero⟩
    | mul_right y hy g hg ih =>
      obtain ⟨j, rfl⟩ := hg
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨q, hq, e⟩ := step hi (by omega : (j : ℕ) < 6)
      exact ⟨q, hq, e.symm⟩
    | mul_inv_cancel y hy g hg ih =>
      obtain ⟨j, rfl⟩ := hg
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨q, hq, e⟩ := step hi (by omega : (j : ℕ) + 3 < 6)
      refine ⟨q, hq, ?_⟩
      rw [← e, ge_inv j.2]
  · rintro ⟨i, -, rfl⟩
    exact xe_mem i

private theorem card_S : Nat.card S = 2 ^ 7 := by
  set f : Fin 128 → J3Model := fun i => xe i.val with hf
  have finj : Function.Injective f := fun i j h => Fin.ext (xe_inj i.2 j.2 h)
  have hset : (S : Set J3Model) = Set.range f := by
    ext y
    rw [SetLike.mem_coe, mem_S_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.2, rfl⟩
  have h1 : Nat.card S = Nat.card (Set.range f) := by
    change Nat.card (S : Set J3Model) = _
    rw [hset]
  rw [h1, Nat.card_congr (Equiv.ofInjective f finj).symm, Nat.card_fin]
  norm_num

private theorem fusion_S (t : J3Model) (ht : t ∈ S) (h1 : t * t = 1) (h2 : t ≠ 1) :
    ∃ k : J3Model, k * uJ 3 * k⁻¹ = t := by
  obtain ⟨i, hi, rfl⟩ := mem_S_iff.1 ht
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact h2 xe_zero
  have hm : clsRel i ∈ invRels ++ clRels ++ clsRels :=
    List.mem_append.2 (Or.inr (List.mem_map.2 ⟨i - 1, List.mem_range.2 (by omega),
      congrArg clsRel (Nat.sub_add_cancel (by omega))⟩))
  have hc := parts.2.2.2.2.1 (i - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hc
  by_cases ho : cls.getD i 0 % 2 = 1
  · have hl : ∀ l ∈ clsRel i, letOK l = true := by
      unfold clsRel
      rw [if_pos ho]
      exact app_ok (app_ok (app_ok (conj_ok _) (by decide)) (inv_ok (conj_ok _)))
        (inv_ok (pw_ok _))
    have h := rel_one hm hl
    unfold clsRel at h
    rw [if_pos ho, ev_append, ev_append, ev_append, ev_four,
      ev_invWordZ fun l hl => letOK_iff.1 (conj_ok _ l hl),
      ev_invWordZ fun l hl => letOK_iff.1 (pw_ok _ l hl)] at h
    exact ⟨_, mul_inv_eq_one.1 h⟩
  · have hq := hc.resolve_left ho
    have hl : ∀ l ∈ clsRel i, letOK l = true := by
      unfold clsRel
      rw [if_neg ho]
      exact app_ok (app_ok (pw_ok _) (pw_ok _)) (inv_ok (pw_ok _))
    have h := rel_one hm hl
    unfold clsRel at h
    rw [if_neg ho, ev_append, ev_append,
      ev_invWordZ fun l hl => letOK_iff.1 (pw_ok _ l hl)] at h
    have e := mul_inv_eq_one.1 h
    change xe i * xe i = xe (cls.getD i 0 / 2) at e
    rw [h1, ← xe_zero] at e
    exact absurd (xe_inj (by omega) hq.2 e) (by omega)

theorem sylowFacts :
    Nat.card (Subgroup.closure (Set.range fun j : Fin 3 => ev (fusGl.getD j []))) = 2 ^ 7 ∧
    ∀ t ∈ Subgroup.closure (Set.range fun j : Fin 3 => ev (fusGl.getD j [])),
      t * t = 1 → t ≠ 1 → ∃ k : J3Model, k * uJ 3 * k⁻¹ = t :=
  ⟨card_S, fusion_S⟩

end CertificateChecks.KernelJ3Fusion

end
