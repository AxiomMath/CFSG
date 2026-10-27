module

public import Certificates.Kernel.FiveStd.SylCov
public import CFSG.Certificates.Kernel.FiveStdKListSound
public import Certificates.Kernel.FiveStd.ClsGlue

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five.FiveStdBase

@[expose] noncomputable def sylRec' (cx cy : Nat) : Bool :=
  orB (andB (memP XP cx) (memP YP cy)) (andB (memP YP cx) (memP XP cy))

theorem sylRec_eq (c : Nat) : sylRec c = sylRec' (cjK c (invK c) 29501) (cjK c (invK c) 78797) := by
  unfold sylRec
  rw [letB_eq, letB_eq, letB_eq]
  rfl

theorem powE_zero (g : E) : powE g 0 = oneE := rfl

theorem map_filter_codeE (L : List E) (p : E → Bool) (q : Nat → Bool) (h : ∀ x, p x = q (codeE x)) :
    (L.filter p).map codeE = (L.map codeE).filter q := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun x _ => h x

theorem codeE_headD (L : List E) (d : E) : codeE (L.headD d) = (L.map codeE).headD (codeE d) := by
  cases L <;> rfl

theorem ord5 (x : E) : (ordE x == 5) = (ordK (codeE x) == 5) := by rw [ordK_codeE]

theorem pow234 (g : E) : ([2, 3, 4].all fun k => decide (codeE g ≤ codeE (powE g k))) =
    ([2, 3, 4].all fun k => decide (codeE g ≤ powK (codeE g) k)) := by
  simp only [powK_codeE]

theorem x1_code : codeE CFSG.GH74.GLS.LU.Local.FiveStd.x1 = 29501 := by
  rw [CFSG.GH74.GLS.LU.Local.FiveStd.x1, codeE_headD, map_filter_codeE _ _ (fun c => ordK c == 5) ord5]
  decide +kernel

theorem y1_code : codeE CFSG.GH74.GLS.LU.Local.FiveStd.y1 = 78797 := by
  rw [CFSG.GH74.GLS.LU.Local.FiveStd.y1, codeE_headD, map_filter_codeE _ _ (fun c => ordK c == 5) ord5]
  decide +kernel

theorem X1cands_codes : X1cands.map codeE = X1c := by
  rw [X1cands, map_filter_codeE _ _ (fun c => [2, 3, 4].all fun k => decide (c ≤ powK c k)) pow234,
    map_filter_codeE _ _ (fun c => ordK c == 5) ord5]
  decide +kernel

theorem Y1cands_codes : Y1cands.map codeE = Y1c := by
  rw [Y1cands, map_filter_codeE _ _ (fun c => [2, 3, 4].all fun k => decide (c ≤ powK c k)) pow234,
    map_filter_codeE _ _ (fun c => ordK c == 5) ord5]
  decide +kernel

theorem r1_nodup : (ppK 29501 78797 5 5).Nodup := by decide +kernel

theorem syl36_nodup : ∀ g ∈ X1c, ∀ h ∈ Y1c, (ppK g h 5 5).Nodup := by decide +kernel

theorem mem_codes {L : List E} {C : List Nat} (h : L.map codeE = C) {c : Nat} (hc : c ∈ C) :
    ∃ x ∈ L, codeE x = c := by
  rw [← h, List.mem_map] at hc
  exact hc

theorem valid_of_code {x : E} {c : Nat} (h : codeE x = c) (hc : validK c = true) : validE x = true := by
  rw [← validK_codeE, h, hc]

theorem mem_pp {gx gy : E} {i j : Nat} (hi : i < 5) (hj : j < 5) :
    mulE (powE gx i) (powE gy j) ∈ ppE gx gy 5 5 := by
  simp only [ppE, mulLL, powers, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩

theorem mulE_oneE {z : E} (hz : validE z = true) : mulE z oneE = z := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hM := Mat.model_ιF (F := ZMod 5)
  apply hM.inj _ _ (hM.valid_mul _ _ hz hM.valid_one) hz
  rw [hM.map_mul _ _ hz hM.valid_one, hM.map_one, mul_one]

theorem oneE_mulE {z : E} (hz : validE z = true) : mulE oneE z = z := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hM := Mat.model_ιF (F := ZMod 5)
  apply hM.inj _ _ (hM.valid_mul _ _ hM.valid_one hz) hz
  rw [hM.map_mul _ _ hM.valid_one hz, hM.map_one, one_mul]

theorem memP_spec {P C : List Nat} (ht : tabOK P C = true) {c : Nat} (h : memP P c = true) :
    ∃ g ∈ C, ∃ j < 5, powK g j = c := by
  obtain ⟨e, he, hc⟩ := List.any_eq_true.1 h
  have := List.all_eq_true.1 ht e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  exact ⟨eG e, List.contains_iff_mem.1 h1, eJ e, h2,
    (Nat.eq_of_beq_eq_true h3).trans (Nat.eq_of_beq_eq_true hc)⟩

theorem pow_of_memP {L : List E} {P C : List Nat} (hL : L.map codeE = C) (ht : tabOK P C = true)
    {x : E} (h : memP P (codeE x) = true) : ∃ g ∈ L, ∃ j < 5, powE g j = x := by
  obtain ⟨c, hc, j, hj, he⟩ := memP_spec ht h
  obtain ⟨g, hg, rfl⟩ := mem_codes hL hc
  exact ⟨g, hg, j, hj, codeE_injective (by rw [← powK_codeE, he])⟩

theorem x1_valid : validE CFSG.GH74.GLS.LU.Local.FiveStd.x1 = true := valid_of_code x1_code (by decide +kernel)

theorem y1_valid : validE CFSG.GH74.GLS.LU.Local.FiveStd.y1 = true := valid_of_code y1_code (by decide +kernel)

theorem cover_pair {cx cy : E} (hx : validE cx = true) (hy : validE cy = true)
    (h : sylRec' (codeE cx) (codeE cy) = true) :
    ∃ q ∈ Syl36, inL cx q.2.2 = true ∧ inL cy q.2.2 = true := by
  unfold sylRec' at h
  rw [orB_eq, andB_eq, andB_eq, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨gx, hgx, j, hj, rfl⟩ := pow_of_memP X1cands_codes tab_x h1
    obtain ⟨gy, hgy, k, hk, rfl⟩ := pow_of_memP Y1cands_codes tab_y h2
    refine ⟨(gx, gy, ppE gx gy 5 5), mem_Syl36.2 ⟨gx, hgx, gy, hgy, rfl⟩, ?_, ?_⟩
    · rw [inL, List.contains_iff_mem]
      have := mem_pp (gx := gx) (gy := gy) hj (Nat.zero_lt_succ 4)
      rwa [powE_zero, mulE_oneE hx] at this
    · rw [inL, List.contains_iff_mem]
      have := mem_pp (gx := gx) (gy := gy) (Nat.zero_lt_succ 4) hk
      rwa [powE_zero, oneE_mulE hy] at this
  · obtain ⟨gy, hgy, j, hj, rfl⟩ := pow_of_memP Y1cands_codes tab_y h1
    obtain ⟨gx, hgx, k, hk, rfl⟩ := pow_of_memP X1cands_codes tab_x h2
    refine ⟨(gx, gy, ppE gx gy 5 5), mem_Syl36.2 ⟨gx, hgx, gy, hgy, rfl⟩, ?_, ?_⟩
    · rw [inL, List.contains_iff_mem]
      have := mem_pp (gx := gx) (gy := gy) (Nat.zero_lt_succ 4) hj
      rwa [powE_zero, oneE_mulE hx] at this
    · rw [inL, List.contains_iff_mem]
      have := mem_pp (gx := gx) (gy := gy) hk (Nat.zero_lt_succ 4)
      rwa [powE_zero, mulE_oneE hy] at this

theorem syl_cover : sylCover = true := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hM := Mat.model_ιF (F := ZMod 5)
  have hgen := (clsOK_spec (clsF_eq 0 ▸ cls_ok 0 (by norm_num))).1
  unfold sylCover
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [nodupL_codeE, R1, map_ppE, x1_code, y1_code]
    exact r1_nodup
  · rw [List.all_eq_true]
    intro q hq
    obtain ⟨gx, hgx, gy, hgy, rfl⟩ := mem_Syl36.1 hq
    rw [nodupL_codeE, map_ppE]
    exact syl36_nodup _ (X1cands_codes ▸ List.mem_map_of_mem hgx) _
      (Y1cands_codes ▸ List.mem_map_of_mem hgy)
  · rw [List.all_eq_true]
    intro c hc
    have hcv := (mem_Cs_iff c).1 hc
    obtain ⟨i, hi, hic⟩ := tree_cover hM (fun l => decE (f20 G l))
      (fun l hl => ⟨valid_decE (hgen l hl).1, codeE_decE (validK_lt (hgen l hl).1)⟩) tree_all c hcv
    have h := (allN_iff _ _).1 (sylc_chunks (i / 900) (by omega)) (i % 900) (Nat.mod_lt _ (by omega))
    have hi' : Nat.add (900 * (i / 900)) (i % 900) = i := by
      rw [nat_add]
      omega
    rw [hi'] at h
    change sylRec (rCode (f64 T i)) = true at h
    rw [hic, sylRec_eq, ← x1_code, ← y1_code, ← codeE_invE, cjK_codeE, cjK_codeE] at h
    obtain ⟨q, hq, h1, h2⟩ := cover_pair (hM.valid_conjE hcv x1_valid) (hM.valid_conjE hcv y1_valid) h
    change (Syl36.any fun q => inL (conjI c (invE c) CFSG.GH74.GLS.LU.Local.FiveStd.x1) q.2.2 &&
      inL (conjI c (invE c) CFSG.GH74.GLS.LU.Local.FiveStd.y1) q.2.2) = true
    rw [Model.conjI_eq, Model.conjI_eq]
    refine List.any_eq_true.2 ⟨q, hq, ?_⟩
    rw [h1, h2]
    rfl

end CertificateChecks.FiveStd

end
