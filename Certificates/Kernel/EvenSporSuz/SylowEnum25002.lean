module

public import Certificates.Kernel.EvenSporSuz.SylowGlue25002
public import Certificates.Kernel.EvenSporSuz.SylowTree25002
public import CFSG.Certificates.Kernel.EvenSporSuz.SylowTreeSound
import all Init.Data.List.SplitOn.Basic

public section

namespace CertificateChecks.KernelSyl25002

open CFSG.KC.EvenSporSuz CFSG.KC.EvenSporSuz.Syl CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec
  CFSG.KC.Str CertificateChecks.KernelSuz CFSG.EvenSporadicStandard.TwoSuz

theorem treeGlob : bindTP tp tokT = true ∧ tp.length = 16383 ∧ ps.length = 16384 ∧
    iv.length = 16384 := by
  have h := treeGlob_true
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem lineT : treeLines.getD 1 "" = String.ofList ((linesK ST.chars).getD 1 []) := by
  unfold treeLines linesK
  rw [ST.eq, nl_eq, splitOn_ofList, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getD_eq_getElem?_getD]
  cases (ST.chars.splitOn '\n')[1]? <;> simp

theorem parse_eq : parseNats (treeLines.getD 1 "") = flatP tp := by
  rw [lineT]
  exact parseNats_of_bindTP treeGlob.1

theorem getD_cons_append {α : Type} (a : α) (B : Array α) (k : ℕ) (d : α) :
    (#[a] ++ B).getD (k + 1) d = B.getD k d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_singleton]
  split
  · omega
  · simp

theorem treePar_size : treePar.size = 16384 := by
  unfold treePar
  simp only [parse_eq, Array.size_append, Array.size_map, Array.size_range, List.size_toArray,
    flatP_length, treeGlob.2.1]
  rfl

theorem treePar_getD {i : ℕ} (hi : i < 16384) (hi0 : i ≠ 0) :
    treePar.getD i (0, 0) = tp.getD (i - 1) (0, 0) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi0
  have hk : k < (flatP tp).toArray.size / 2 := by
    simp only [List.size_toArray, flatP_length, treeGlob.2.1]
    omega
  unfold treePar
  rw [parse_eq, getD_cons_append, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range, if_pos hk, Option.map_some, Option.getD_some, Nat.add_sub_cancel]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  obtain ⟨h1, h2⟩ := flatP_getD tp k
  rw [h1, h2]

theorem tree : (∃ h : ps.getD 0 0 < ed.length, (ed[ps.getD 0 0]).1 = one3) ∧
    (∀ i < 16384, i ≠ 0 → (tp.getD (i - 1) (0, 0)).1 < i ∧ (tp.getD (i - 1) (0, 0)).2 < 4 ∧
      ∃ (h : ps.getD i 0 < ed.length) (h' : ps.getD (tp.getD (i - 1) (0, 0)).1 0 < ed.length),
        (ed[ps.getD i 0]).1 = mulF3 (ed[ps.getD (tp.getD (i - 1) (0, 0)).1 0]).1
          (gs.getD (tp.getD (i - 1) (0, 0)).2 0)) ∧
    (∀ j < 16384, ∃ h : iv.getD j 0 < 16384, ps.getD (iv.getD j 0) 0 = j) := by
  refine tree_sound (fun c hc => ?_) treeGlob.2.2.1 treeGlob.2.2.2 treeGlob.2.1
  interval_cases c
  exacts [tr250020, tr250021, tr250022, tr250023]

theorem sMats_getD {g : ℕ} (hg : g < 4) : sMats.getD g oneM = jMats.getD g oneM := by
  have hs : jMats.size = 5 := by
    simp only [jMats, List.size_toArray, List.length_map, jWords_eq, jW]
    simp
  unfold sMats
  rw [ngS_eq, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  simp only [hs]
  rw [if_pos (by omega), Nat.zero_add]

theorem lanes_buildE : ∀ i < 16384, ∃ h : ps.getD i 0 < ed.length,
    lanesMt ((buildE sMats treePar).getD i oneM) = (ed[ps.getD i 0]).1 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · obtain ⟨h, h1⟩ := tree.1
    exact ⟨h, by rw [buildE_getD_zero, lanesMt_oneM, h1]⟩
  obtain ⟨hp, hg, h, h', he⟩ := tree.2.1 i hi (by omega)
  refine ⟨h, ?_⟩
  have hpar := treePar_getD hi (by omega)
  have hcg : canonB (sMats.getD (tp.getD (i - 1) (0, 0)).2 oneM) = true := by
    rw [sMats_getD hg]
    exact jCanon.1 _
  obtain ⟨_, hip⟩ := ih _ hp (by omega)
  rw [buildE_getD sMats (by rw [treePar_size]; exact hi) (by omega) (by rw [hpar]; exact hp), hpar,
    ← mulF3_lanesMt (canonB_buildE _ _ _) hcg, hip, sMats_getD hg, ← gs_getD hg]
  exact he.symm

theorem buildE_size' : (buildE sMats treePar).size = 16384 := by
  rw [buildE_size sMats (by rw [treePar_size]; norm_num), treePar_size]

theorem ofMt_buildE {i : ℕ} (hi : i < 16384) : ∃ h : ps.getD i 0 < ed.length,
    ofMt ((buildE sMats treePar).getD i oneM) = pkMat3 (ed[ps.getD i 0]).1 := by
  obtain ⟨h, he⟩ := lanes_buildE i hi
  exact ⟨h, by rw [← he, pkMat3_lanesMt (canonB_buildE _ _ _)]⟩

theorem enum {s : GL12} (hs : s ∈ sylS) : ∃ i < (buildE sMats treePar).size,
    ofMt ((buildE sMats treePar).getD i oneM) = vm s := by
  obtain ⟨p, hp, hpe⟩ := enum_fwd hs
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hp
  have hj' : j < 16384 := by rw [← facts.len]; exact hj
  obtain ⟨hi, hij⟩ := tree.2.2 j hj'
  obtain ⟨h, he⟩ := ofMt_buildE hi
  refine ⟨iv.getD j 0, by rw [buildE_size']; exact hi, ?_⟩
  rw [he, ← hpe]
  simp only [hij]

theorem enum_mem {i : ℕ} (hi : i < (buildE sMats treePar).size) :
    ∃ u ∈ sylS, vm u = ofMt ((buildE sMats treePar).getD i oneM) := by
  rw [buildE_size'] at hi
  obtain ⟨h, he⟩ := ofMt_buildE hi
  rw [he]
  exact enum_back (List.getElem_mem h)

end CertificateChecks.KernelSyl25002
