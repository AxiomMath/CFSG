
module

public import Certificates.Kernel.OmegaEight.SB3873A
public import Certificates.Kernel.OmegaEight.SBChunks
public import Certificates.Kernel.OmegaEight.SB3871Blocks
public import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coord
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8

@[expose] def look (L : List (ℕ × ℕ)) (u : ℕ) : ℕ := ((L.find? fun p => p.1 == u).map Prod.snd).getD 0

@[expose] noncomputable def clsAt (k m z : ℕ) (r : ℕ × ℕ) : Bool :=
  decide (r.1 < 131072) && MK k m z r.1 r.1 == 0 && r.1 != 0 &&
    orbOKM (MK k m z) (IK k m z) 131072 r.1 (recM (MK k m z) (IK k m z) t1Gens r.1) &&
    orbClosedM (MK k m z) (IK k m z) t1Gens r.1 (recM (MK k m z) (IK k m z) t1Gens r.1) &&
    (recM (MK k m z) (IK k m z) t1Gens r.1).length == r.2 &&
    (recM (MK k m z) (IK k m z) t1Gens r.1).all fun p => decide (r.1 ≤ p.1)

@[expose] def PartA (k m z : ℕ) : Prop :=
  (∀ s < 8, conjOK k m z (8192 * s) 8192 = true) ∧ wOK k m = true ∧ lOK k = true ∧
    chiWOK k m = true ∧ chiLOK k = true ∧ z < 65536 ∧ (chiS 65536)[z]! = false

@[expose] def PartC (k m z : ℕ) (rows : List (List ℕ)) : Prop :=
  (∀ s < 16, ((chunks 8 16 (t1Cls k m z)).getD s []).all (clsAt k m z) = true) ∧
    (t1Cls k m z).length ≤ 128 ∧
    (((t1Cls k m z).zip (t1Cls k m z).tail).all fun p => decide (p.1.1 < p.2.1)) = true ∧
    ((t1Cls k m z).map Prod.snd).sum = rows.flatten.length

@[expose] def PartB (k m z : ℕ) (rows : List (List ℕ)) : Prop :=
  rows.length = 16 ∧ ∀ s < 16,
    ((List.range' (8192 * s) 8192).filter fun c => MK k m z c c == 0 && c != 0) = rows.getD s []

@[expose] def PartO (k m z : ℕ) (U : List ℕ) (acc : List (List (ℕ × ℕ))) : Prop :=
  acc.getD 0 [] = U.map (fun u => (u, 0)) ∧ ∀ s < 16,
    (List.range' (8192 * s) 8192).foldl (ord4Step (MK k m z)) (acc.getD s []) = acc.getD (s + 1) []

@[expose] def PartK (k m z : ℕ) (n5 : Bool) (rows : List (List ℕ)) (U : List ℕ)
    (acc : List (List (ℕ × ℕ))) : Prop :=
  ∀ p ∈ sMarked, killAtCF (MK k m z) (IK k m z) t1Gens 131072 rows.flatten
      (kRepsC (t1Cls k m z) 8) (look (acc.getD 16 [])) 8 (chiS 131072) n5 p.1 p.2 = true ∧
    queriedIn (MK k m z) (IK k m z) t1Gens rows.flatten (kRepsC (t1Cls k m z) 8) 8 (chiS 131072) n5
      p.1 p.2 U = true

theorem range_blocks : List.range 131072 =
    ((List.range 16).map fun s => List.range' (8192 * s) 8192).flatten := by
  rw [← List.flatMap_def, ← range_mul_eq_flatMap]

theorem kInv_of_partB {k m z : ℕ} {rows : List (List ℕ)} (h : PartB k m z rows) :
    kInv (MK k m z) 131072 = rows.flatten := by
  unfold kInv
  rw [range_blocks]
  refine filter_blocks _ _ _ (by simp [h.1]) fun s hs => ?_
  simp only [List.length_map, List.length_range] at hs
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs, Option.map_some,
    Option.getD_some]
  exact h.2 s hs

theorem look_map (U : List ℕ) (f : ℕ → ℕ) {u : ℕ} (hu : u ∈ U) :
    look (U.map fun v => (v, f v)) u = f u := by
  induction U with
  | nil => simp at hu
  | cons v U ih =>
    by_cases hv : v = u
    · subst hv
      simp [look]
    · have hu' : u ∈ U := (List.mem_cons.1 hu).resolve_left (Ne.symm hv)
      rw [← ih hu']
      simp [look, hv]

theorem look_of_partO {k m z : ℕ} {U : List ℕ} {acc : List (List (ℕ × ℕ))}
    (h : PartO k m z U acc) {u : ℕ} (hu : u ∈ U) :
    look (acc.getD 16 []) u = kCount (MK k m z) (kOrd4 (MK k m z) 131072) u := by
  have hchain : (List.range 131072).foldl (ord4Step (MK k m z)) (acc.getD 0 []) = acc.getD 16 [] := by
    rw [show (131072 : ℕ) = 8192 * 16 from rfl, foldl_range_blocks]
    exact foldl_range_chain _ (fun s => acc.getD s []) 16 h.2
  rw [← hchain, h.1, foldl_ord4Step, List.map_map]
  have e := look_map U (fun v => 0 + ((List.range 131072).filter fun c =>
    isOrd4 (MK k m z) c && MK k m z c v == MK k m z v c).length) hu
  simp only [Function.comp_def] at e ⊢
  rw [e, kCount_kOrd4_eq, Nat.zero_add]

theorem clsOK_of_parts {k m z : ℕ} {rows : List (List ℕ)} (hC : PartC k m z rows)
    (hB : PartB k m z rows) :
    kClassOK (MK k m z) (IK k m z) t1Gens 131072 (t1Cls k m z) = true := by
  obtain ⟨hblk, hlen, hsort, hsum⟩ := hC
  unfold kClassOK
  rw [Bool.and_eq_true, Bool.and_eq_true, kInv_of_partB hB, hsort, hsum, beq_self_eq_true]
  refine ⟨⟨rfl, ?_⟩, rfl⟩
  rw [← chunks_flatten 8 16 (t1Cls k m z) hlen]
  refine all_blocks _ _ fun s hs => ?_
  rw [chunks_length] at hs
  exact hblk s hs

theorem t1KillC_of_parts {k m z : ℕ} {n5 : Bool} {rows : List (List ℕ)} {U : List ℕ}
    {acc : List (List (ℕ × ℕ))} (hA : PartA k m z) (hC : PartC k m z rows) (hB : PartB k m z rows)
    (hO : PartO k m z U acc) (hK : PartK k m z n5 rows U acc) : t1KillC k m z n5 = true := by
  obtain ⟨hconj, hw, hl, hcw, hcl, hz, hzχ⟩ := hA
  have hconj' : conjOK k m z 0 65536 = true := by
    unfold conjOK
    rw [List.all_eq_true]
    intro y hy
    rw [List.mem_range'_1] at hy
    have hs : y / 8192 < 8 := by omega
    have := hconj _ hs
    unfold conjOK at this
    rw [List.all_eq_true] at this
    exact this y (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  refine t1KillC_of hw hl hconj' hz hzχ hcw hcl (clsOK_of_parts hC hB) fun p hp => ?_
  obtain ⟨hk, hq⟩ := hK p hp
  rw [killAtC, kInv_of_partB hB, killAtCF_congr (MK k m z) (IK k m z) t1Gens 131072 _ _ _
    (look (acc.getD 16 [])) _ _ _ _ _ U hq fun u hu => (look_of_partO hO hu).symm]
  exact hk

theorem t1Kill_eq (k m z : ℕ) (n5 : Bool) : t1Kill k m z n5 sMarked = t1KillC k m z n5 := rfl

theorem t1KillRange_of (a : ℕ) (h : ∀ i < 64, a ≤ i → i < a + 10 →
    t1KillC t1List[i]!.1 t1List[i]!.2.1 t1List[i]!.2.2.1 t1List[i]!.2.2.2 = true) :
    t1KillRange a = true := by
  unfold t1KillRange
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
  have hl : t1List.length = 64 := by decide
  simp only [List.length_take, List.length_drop, hl] at hj
  rw [List.getElem_take, List.getElem_drop, t1Kill_eq]
  have := h (a + j) (by omega) (by omega) (by omega)
  rwa [getElem!_pos t1List (a + j) (by omega)] at this

macro "t1kill " rows:term ", " U:term ", " acc:term : tactic => `(tactic| (
  refine t1KillC_of_parts (rows := $rows) (U := $U) (acc := $acc) ?_ ?_ ?_ ?_ ?_
  · refine ⟨fun s hs => ?_, by decide +kernel, by decide +kernel, ?_, ?_, by decide, ?_⟩
    · interval_cases s <;> decide +kernel
    · simp only [chiWOK, chiS_get]
      decide +kernel
    · simp only [chiLOK, chiS_get]
      decide +kernel
    · rw [chiS_get]
      decide +kernel
  · refine ⟨fun s hs => ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
    interval_cases s <;> decide +kernel
  · refine ⟨by decide +kernel, fun s hs => ?_⟩
    interval_cases s <;> decide +kernel
  · refine ⟨by decide +kernel, fun s hs => ?_⟩
    interval_cases s <;> decide +kernel
  · unfold PartK
    simp only [sMarked, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_⟩ <;>
      (simp only [killAtCF, queriedIn, chiS_get]; exact ⟨by decide +kernel, by decide +kernel⟩)))

end CertificateChecks.KernelO8.SB3873

end
