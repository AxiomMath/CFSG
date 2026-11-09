module

public import CFSG.Certificates.Kernel.J4M4Sound
public import CFSG.Certificates.Kernel.Misc.F2BfsRec2Sound
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
  (hC : ∀ s < L.length, ∀ k ∈ SL, actR (L.map ccK) s k ∈ SL)
include hT hC

theorem hT' : oneK ∈ SL ∧ (∀ k ∈ SL, ReachN (actR (L.map ccK)) (L.map cc).length oneK 64 k) ∧
    SL.Nodup := by
  rwa [List.length_map]

theorem hC' : ∀ s < (L.map cc).length, ∀ k ∈ SL, actR (L.map ccK) s k ∈ SL := by
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

theorem mulW_assoc12 (a b c : ℕ) : mulW 12 (mulW 12 a b) c = mulW 12 a (mulW 12 b c) := by
  simp only [mulW_eq]
  exact CFSG.KC.F2Mat.matOfF_inj (CFSG.KC.F2BfsRec.mulF_lt _ _ _) (CFSG.KC.F2BfsRec.mulF_lt _ _ _)
    (by simp only [CFSG.KC.F2Mat.matOfF_mulF, mul_assoc])

theorem mem_runs_iff {α : Type} (c m : ℕ) (L : List α) (h : L.length = c * m) (x : α) :
    x ∈ L ↔ ∃ i < c, x ∈ (L.drop (m * i)).take m := by
  induction c generalizing L with
  | zero =>
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at h
    subst h
    simp
  | succ c ih =>
    have hd : (L.drop m).length = c * m := by
      rw [List.length_drop, h, Nat.succ_mul, Nat.add_sub_cancel]
    have e : x ∈ L ↔ x ∈ L.take m ∨ x ∈ L.drop m := by
      conv_lhs => rw [← List.take_append_drop m L]
      exact List.mem_append
    rw [e, ih _ hd]
    constructor
    · rintro (hx | ⟨i, hi, hx⟩)
      · exact ⟨0, by omega, by simpa using hx⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [List.drop_drop] at hx
        rwa [Nat.mul_add_one, Nat.add_comm]
    · rintro ⟨i, hi, hx⟩
      cases i with
      | zero => exact Or.inl (by simpa using hx)
      | succ i =>
        refine Or.inr ⟨i, by omega, ?_⟩
        rw [List.drop_drop]
        rwa [Nat.mul_add_one, Nat.add_comm] at hx

theorem mem_TN {x : ℕ} : x ∈ KL ↔ ∃ t ∈ TL, ∃ n ∈ NL, mulW 12 t n = x := by
  have hT := tLen_k
  rw [mem_runs_iff 16 1024 KL bound_parts.2.1 x]
  constructor
  · rintro ⟨i, hi, hx⟩
    rw [← (eqL_iff _ _).mp (tn_k i hi), (msort_perm _).mem_iff, List.mem_flatMap] at hx
    obtain ⟨t, ht, hx⟩ := hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    exact ⟨t, (mem_runs_iff 16 16 TL hT t).mpr ⟨i, hi, ht⟩, n, hn, rfl⟩
  · rintro ⟨t, ht, n, hn, rfl⟩
    obtain ⟨i, hi, ht⟩ := (mem_runs_iff 16 16 TL hT t).mp ht
    refine ⟨i, hi, ?_⟩
    rw [← (eqL_iff _ _).mp (tn_k i hi), (msort_perm _).mem_iff, List.mem_flatMap]
    exact ⟨t, ht, List.mem_map_of_mem hn⟩

theorem K_close : ∀ s < 10, ∀ k ∈ KL, mulW 12 k (KG.getD s 0) ∈ KL := by
  intro s hs k hk
  obtain ⟨t, ht, n, hn, rfl⟩ := mem_TN.mp hk
  have hN := (eqL_iff _ _).mp (List.all_eq_true.mp nnorm_k s (List.mem_range.mpr hs))
  have h1 : mulW 12 n (KG.getD s 0) ∈ msort (NL.map (mulW 12 (KG.getD s 0))) := by
    rw [← hN, (msort_perm _).mem_iff]
    exact List.mem_map_of_mem hn
  rw [(msort_perm _).mem_iff, List.mem_map] at h1
  obtain ⟨c, hc, hce⟩ := h1
  have h2 : mulW 12 t (KG.getD s 0) ∈ KL := by
    refine subF_sound _ _ _ tgen_k _ ?_
    rw [(msort_perm _).mem_iff, List.mem_flatMap]
    exact ⟨t, ht, List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩⟩
  obtain ⟨t', ht', n', hn', he⟩ := mem_TN.mp h2
  have h3 : mulW 12 n' c ∈ NL := by
    rw [← (eqL_iff _ _).mp (List.all_eq_true.mp ncl_k n' hn'), (msort_perm _).mem_iff]
    exact List.mem_map_of_mem hc
  refine mem_TN.mpr ⟨t', ht', _, h3, ?_⟩
  rw [mulW_assoc12 t, ← hce, ← mulW_assoc12 t (KG.getD s 0) c, ← he, mulW_assoc12 t' n' c]

theorem K_C : ∀ s < kGens.length, ∀ k ∈ KL, actR (kGens.map ccK) s k ∈ KL := by
  rw [← bound_parts.2.2, len_k.2]
  exact K_close

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
  replace hC := closeOK_sound hC
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
