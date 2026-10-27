module

public import CFSG.Certificates.Kernel.J4M4Sound
public import Certificates.Kernel.J4M4.Misc
public import Certificates.Kernel.J4M4.Small
public import Certificates.Kernel.J4M4.KTree
public import Certificates.Kernel.J4M4.KClose
public import Certificates.Kernel.J4M4.Orbits

public section

namespace CertificateChecks.KernelJ4M4

open CFSG.KC.J4M4 CFSG.KC.J4Tree CFSG.KC.F2W CFSG.J4Tree.Native CFSG.J4Tree.Native.Node
open CFSG.J4Tree.M4 CFSG.KC.Co1F2

theorem rc_gen (L : List (ℕ × ℕ)) :
    ∀ s < (L.map cc).length, RC ((L.map cc).getD s 1) ((L.map ccK).getD s 0) :=
  fun _ hs => rc_map_getD u_wf k_wf L (by simpa using hs)

theorem rc_of_rows {a : Code} {K : ℕ} (h : eqL a.rows.toList (fieldsL K) = true) : RC a K := by
  rw [eqL_iff, fieldsL_eq] at h
  exact Array.ext' h

theorem wf_of_rc {a : Code} {K : ℕ} (h : RC a K) : a.wf = true := by
  have e : a.rows.toList = fieldsL K := by rw [h, fieldsL_eq]
  unfold Code.wf
  rw [Bool.and_eq_true, beq_iff_eq, ← Array.length_toList, e, List.all_eq_true]
  refine ⟨by simp [fieldsL], fun x hx => ?_⟩
  simp only [fieldsL, List.mem_map, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact decide_eq_true (Nat.mod_lt _ (by norm_num))

theorem rc_cc' (ce : ℕ × ℕ) : RC (cc ce) (ccK ce) := rc_cc u_wf k_wf ce

theorem contains_iff {l : List ℕ} {a : ℕ} : l.contains a = true ↔ a ∈ l := by simp

theorem closure_eq (G : List Code) : closureOf G = bfsFrom G rmul 1 64 := rfl

theorem orbit_eq (gp : List (Code × Code)) (x : Code) : orbitOf gp x = bfsFrom gp conjP x 64 := rfl

section Sets

variable {L : List (ℕ × ℕ)} {SL : List ℕ}
  (hT : oneK ∈ SL ∧ (∀ k ∈ SL, ReachN (actR (L.map ccK)) L.length oneK 64 k) ∧ SL.Nodup)
  (hC : closeOK (actR (L.map ccK)) L.length SL = true)
include hT hC

theorem hT' : oneK ∈ SL ∧ (∀ k ∈ SL, ReachN (actR (L.map ccK)) (L.map cc).length oneK 64 k) ∧
    SL.Nodup := by
  rwa [List.length_map]

theorem hC' : closeOK (actR (L.map ccK)) (L.map cc).length SL = true := by
  rwa [List.length_map]

theorem set_mem (y : Code) : y ∈ closureOf (L.map cc) ↔ ∃ k ∈ SL, RC y k := by
  rw [closure_eq]
  exact mem_of_cert (d := 1) (rmul_step (rc_gen L)) rc_one (hT' hT hC) (hC' hT hC) y

theorem set_sub : subOK (L.map cc) (closureOf (L.map cc)) = true := by
  obtain ⟨h1, h2⟩ := closed_of_cert (d := 1) (rmul_step (rc_gen L)) rc_one (hT' hT hC) (hC' hT hC)
  unfold subOK
  rw [closure_eq, h1, h2]
  rfl

theorem set_contains {y : Code} {k : ℕ} (hy : RC y k) (hk : SL.contains k = true) :
    (closureOf (L.map cc)).contains y = true := by
  rw [closure_eq]
  exact contains_of_cert (d := 1) (rmul_step (rc_gen L)) rc_one (hT' hT hC) (hC' hT hC) hy
    (contains_iff.mp hk)

theorem set_not_contains {y : Code} {k : ℕ} (hy : RC y k)
    (hk : SL.all (fun k' => !eqC k' k) = true) : (closureOf (L.map cc)).contains y = false := by
  rw [closure_eq]
  exact not_contains_of_cert (d := 1) (rmul_step (rc_gen L)) rc_one (hT' hT hC) (hC' hT hC) hy hk

theorem set_size (hb : SL.all (fun k => Nat.blt k (2 ^ 144)) = true) :
    (closureOf (L.map cc)).size = SL.length := by
  rw [closure_eq]
  exact size_of_cert (d := 1) (rmul_step (rc_gen L)) rc_one (hT' hT hC) (hC' hT hC) hb

end Sets

theorem bound_parts : KL.all (fun k => Nat.blt k (2 ^ 144)) = true ∧ KL.length = 16384 ∧
    KG = kGens.map ccK := by
  have h := bound_k
  unfold boundK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, eqL_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem small_parts :
    (certOK (actR (fBasis.map ccK)) fBasis.length oneK FL FY = true ∧
      closeOK (actR (fBasis.map ccK)) fBasis.length FL = true) ∧
    (certOK (actR ((treeWv 539).map ccK)) (treeWv 539).length oneK WL WY = true ∧
      closeOK (actR ((treeWv 539).map ccK)) (treeWv 539).length WL = true) ∧
    (certOK (actR ((treeBasis 539).map ccK)) (treeBasis 539).length oneK RL RY = true ∧
      closeOK (actR ((treeBasis 539).map ccK)) (treeBasis 539).length RL = true) ∧
    (certOK (actR (y136.map ccK)) y136.length oneK Y1L Y1Y = true ∧
      closeOK (actR (y136.map ccK)) y136.length Y1L = true) ∧
    (certOK (actR (y266.map ccK)) y266.length oneK Y2L Y2Y = true ∧
      closeOK (actR (y266.map ccK)) y266.length Y2L = true) := by
  have h := small_k
  have hf : fBasis.length = 10 := by decide
  unfold smallK at h
  rw [hf]
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩, ⟨h9, h10⟩⟩

theorem layK_all : ∀ n < 10, layK n = true := by
  intro n hn
  interval_cases n
  exacts [layK0, layK1, layK2, layK3, layK4, layK5, layK6, layK7, layK8, layK9]

theorem K_T : oneK ∈ KL ∧ (∀ k ∈ KL, ReachN (actR (kGens.map ccK)) kGens.length oneK 64 k) ∧
    KL.Nodup := by
  rw [← bound_parts.2.2, len_k.2]
  refine certHead_sound headK_ok fun d h1 h2 => ?_
  rw [len_ky] at h2
  have hd : d - 1 < 10 := by omega
  have e : d = d - 1 + 1 := by omega
  rw [e]
  exact layK_all (d - 1) hd

theorem K_C : closeOK (actR (kGens.map ccK)) kGens.length KL = true := by
  rw [← bound_parts.2.2, len_k.2, closeOK, List.all_eq_true]
  intro s hs
  have hs' := List.mem_range.mp hs
  interval_cases s
  exacts [closeKS0, closeKS1, closeKS2, closeKS3, closeKS4, closeKS5, closeKS6, closeKS7, closeKS8,
    closeKS9]

theorem gp_len : (pairsOf (kGens.map cc)).length = 10 := by
  rw [pairsOf, List.length_map, List.length_map]
  exact len_k.2

theorem gp_rc : ∀ s < (pairsOf (kGens.map cc)).length,
    RC ((pairsOf (kGens.map cc)).getD s (1, 1)).1 (KG.getD s 0) ∧
      RC ((pairsOf (kGens.map cc)).getD s (1, 1)).2 (KGI.getD s 0) := by
  intro s hs
  have hs10 : s < 10 := gp_len ▸ hs
  have hl : s < (kGens.map cc).length := by rw [List.length_map, len_k.2]; exact hs10
  have e : (pairsOf (kGens.map cc)).getD s (1, 1) =
      ((kGens.map cc).getD s 1, ((kGens.map cc).getD s 1).inv) := by
    rw [List.getD_eq_getElem _ _ hs, List.getD_eq_getElem _ _ hl]
    simp [pairsOf]
  rw [e]
  refine ⟨by rw [bound_parts.2.2]; exact rc_gen kGens s hl, rc_of_rows ?_⟩
  have h := List.all_eq_true.mp inv_k ((kGens.map cc)[s], KGI[s]'(by rw [len_k.1]; exact hs10))
    (by
      rw [List.mem_iff_getElem]
      refine ⟨s, by simp [len_k.1, len_k.2, hs10], ?_⟩
      simp)
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by rw [len_k.1]; exact hs10)]
  exact h

theorem all_blocks {β : Type} (L : List β) (p : β → Bool) (b m : ℕ) (hb : 0 < b)
    (h : ∀ n < m, ((L.drop (b * n)).take b).all p = true) (hl : L.length ≤ b * m) :
    L.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hn : i / b < m := by
    rw [Nat.div_lt_iff_lt_mul hb]
    rw [Nat.mul_comm] at hl
    omega
  have e : b * (i / b) + i % b = i := Nat.div_add_mod i b
  have hmod : i % b < b := Nat.mod_lt i hb
  refine List.all_eq_true.mp (h (i / b) hn) _ (List.mem_iff_getElem.mpr ⟨i % b, ?_, ?_⟩)
  · simp only [List.length_take, List.length_drop]
    omega
  · simp only [List.getElem_take, List.getElem_drop, e]

theorem ir_all : IR.all irOK = true :=
  all_blocks IR irOK 256 12 (by norm_num) (fun n hn => by
    interval_cases n
    exacts [irK0, irK1, irK2, irK3, irK4, irK5, irK6, irK7, irK8, irK9, irK10, irK11])
    len_ir.1

theorem cl_all : CL.all clOK = true :=
  all_blocks CL clOK 64 7 (by norm_num) (fun n hn => by
    interval_cases n
    exacts [clK0, clK1, clK2, clK3, clK4, clK5, clK6]) len_ir.2

theorem cl_getD (i : ℕ) : clOK (CL.getD i []) = true := by
  by_cases hi : i < CL.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.all_eq_true.mp cl_all _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    decide

theorem orbit_of_rec {x : Code} {r : ℕ × ℕ × List (List (ℕ × ℕ × ℕ))} (hr : r ∈ IR)
    (hx : RC x r.1) :
    orbOK (pairsOf (kGens.map cc)) x (orbitOf (pairsOf (kGens.map cc)) x) = true ∧
      (orbitOf (pairsOf (kGens.map cc)) x).size = (CL.getD r.2.1 []).length ∧
      ((CL.getD r.2.1 []).length = 4 → FL.contains r.1 = true) := by
  have h := List.all_eq_true.mp ir_all r hr
  unfold irOK at h
  rw [Bool.and_eq_true, Bool.or_eq_true] at h
  have hc := cl_getD r.2.1
  unfold clOK at hc
  rw [Bool.and_eq_true] at hc
  have hT : certOK (actC KG KGI) (pairsOf (kGens.map cc)).length r.1 (CL.getD r.2.1 []) r.2.2 =
      true := by rw [gp_len]; exact h.1
  have hC : closeOK (actC KG KGI) (pairsOf (kGens.map cc)).length (CL.getD r.2.1 []) = true := by
    rw [gp_len]; exact hc.1
  replace hT := certOK_sound hT
  obtain ⟨h1, h2⟩ := closed_of_cert (d := (1, 1)) (conj_step gp_rc) hx hT hC
  refine ⟨?_, ?_, fun h4 => ?_⟩
  · unfold orbOK
    rw [orbit_eq, h1, h2]
    rfl
  · rw [orbit_eq]
    exact size_of_cert (d := (1, 1)) (conj_step gp_rc) hx hT hC hc.2
  · rcases h.2 with h' | h'
    · rw [h4] at h'
      exact absurd h' (by decide)
    · exact h'

end CertificateChecks.KernelJ4M4
