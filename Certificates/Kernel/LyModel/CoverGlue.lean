
module

public import Certificates.Kernel.LyModel.Tab
public import Certificates.Kernel.LyModel.NetChk
public import Certificates.Kernel.LyModel.Cover
public import Certificates.Kernel.LyBase.Facts

public section

namespace CertificateChecks.KernelLyModel

open Equiv CFSG.KC CFSG.KC.Benes CFSG.KC.YModel.Sem CFSG.KC.LyBenes CFSG.KC.LyModel
  CFSG.KC.MonsterConv.Perm CertificateChecks.KernelLy CertificateChecks.KernelLyB
  CertificateChecks.KernelLyBase CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.Sporadic.Recognition.McLMultiplier
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem validM : ∀ j < 8, StagesValid 17 (MS j) := fun j hj =>
  stagesValid_of_netValid (ly6110_validM j hj)

theorem nrep_word {gs : ℕ → Perm (Fin Ly0.deg)} {net : ℤ → Nat} {w : List ℤ}
    (hn : ∀ z ∈ w, NRep 17 Ly0.deg (net z) (Ly0.letterG gs z))
    (hv : ∀ z ∈ w, StagesValid 17 (net z)) {N : Nat} (hN : StagesValid 17 N)
    (h : planesEq 17 (w.map net) N = true) : NRep 17 Ly0.deg N (Ly0.wG gs w) := by
  have hv' : ∀ M ∈ w.map net, StagesValid 17 M := by
    intro M hM
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hM
    exact hv z hz
  have e := planesEq_sound hv' hN h
  intro a
  rw [← e a (lt_of_lt_of_le a.2 deg_le), compN_map net _ w hn a, wG_eq_prod]

theorem nrep_A : NRep 17 Ly0.deg (MS 0) Ly0.AG := by
  rw [Ly0.AG_def]
  exact nrep_word (fun z hz => nrep_z cL_eq_cG dL_eq_dG z (Ly0.decodeWord_mem _ z hz))
    (fun z hz => valid_all _ (zIdx_lt z (Ly0.decodeWord_mem _ z hz))) (validM 0 (by decide))
    ly6110_netA

theorem nrep_B : NRep 17 Ly0.deg (MS 1) Ly0.BG := by
  rw [Ly0.BG_def]
  exact nrep_word (fun z hz => nrep_z cL_eq_cG dL_eq_dG z (Ly0.decodeWord_mem _ z hz))
    (fun z hz => valid_all _ (zIdx_lt z (Ly0.decodeWord_mem _ z hz))) (validM 1 (by decide))
    ly6110_netB

theorem invW_mem {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 2) :
    ∀ z ∈ invW w, z ≠ 0 ∧ z.natAbs ≤ 2 := by
  intro z hz
  simp only [invW, List.mem_reverse, List.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have := hw y hy
  omega

theorem nrep_Bi : NRep 17 Ly0.deg (MS 2) Ly0.BG⁻¹ := by
  have h := nrep_word (gs := Ly0.gens0) (w := invW Ly0.wordB)
    (fun z hz => nrep_z cL_eq_cG dL_eq_dG z (invW_mem (Ly0.decodeWord_mem _) z hz))
    (fun z hz => valid_all _ (zIdx_lt z (invW_mem (Ly0.decodeWord_mem _) z hz)))
    (validM 2 (by decide)) ly6110_netBi
  have hB : ∀ l ∈ Ly0.wordB, l ≠ 0 := fun l hl => (Ly0.decodeWord_mem _ l hl).1
  rwa [Ly0.wG_invW Ly0.gens0 hB, ← Ly0.BG_def] at h

theorem pair_id {i j : Nat} (hi : i < 8) (hj : j < 8) (h : planesId 17 [MS i, MS j] = true) :
    ∀ r < 2 ^ 17, compN 17 [MS i, MS j] r = r := by
  refine planesId_sound (fun N hN => ?_) h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
  rcases hN with rfl | rfl
  · exact validM i hi
  · exact validM j hj

theorem nrep_z1 (z : ℤ) (hz : z ≠ 0 ∧ z.natAbs ≤ 2) :
    NRep 17 Ly0.deg (MS (zIdx z)) (Ly0.letterG Ly0.gens1 z) := by
  have : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · have e : Ly0.letterG Ly0.gens1 1 = Ly0.AG := by simp [Ly0.letterG_pos, Ly0.gens1_zero]
    rw [e]
    exact nrep_A
  · have e : Ly0.letterG Ly0.gens1 (-1) = Ly0.AG⁻¹ := by
      simp [Ly0.letterG_neg_of, Ly0.gens1_zero]
    rw [e]
    exact nrep_A.inv deg_le (pair_id (by decide) (by decide) ly6110_netAA)
  · have e : Ly0.letterG Ly0.gens1 2 = Ly0.BG := by simp [Ly0.letterG_pos, Ly0.gens1_one]
    rw [e]
    exact nrep_B
  · have e : Ly0.letterG Ly0.gens1 (-2) = Ly0.BG⁻¹ := by
      simp [Ly0.letterG_neg_of, Ly0.gens1_one]
    rw [e]
    exact nrep_Bi

theorem zIdx_lt8 (z : ℤ) (hz : z ≠ 0 ∧ z.natAbs ≤ 2) : zIdx z < 8 := by
  have : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

theorem genWord_mem {k : Nat} (hk : k < 6) : ∀ z ∈ mclGenWord k, z ≠ 0 ∧ z.natAbs ≤ 2 := by
  intro z hz
  interval_cases k <;> simp [mclGenWord] at hz <;> omega

theorem nrep_y {k : Nat} (hk : k < 5) : NRep 17 Ly0.deg (MS (k + 3)) (Ly0.yG k) := by
  rw [Ly0.yG_def]
  have hY : planesEq 17 (genNets MS (mclGenWord k)) (MS (k + 3)) = true := by
    interval_cases k
    exacts [ly6110_netY0, ly6110_netY1, ly6110_netY2, ly6110_netY3, ly6110_netY4]
  exact nrep_word (fun z hz => nrep_z1 z (genWord_mem (by omega) z hz))
    (fun z hz => validM _ (zIdx_lt8 z (genWord_mem (by omega) z hz))) (validM _ (by omega)) hY

theorem yG_five' : Ly0.yG 5 = Ly0.AG := by
  rw [Ly0.yG_def]
  have e : mclGenWord 5 = [1] := rfl
  rw [e, Ly0.wG_cons, Ly0.wG_nil, mul_one]
  simp [Ly0.letterG_pos, Ly0.gens1_zero]

theorem beq_five_false {i : Fin 6} (h : i.val < 5) : Nat.beq i.val 5 = false :=
  Bool.eq_false_iff.2 fun e => absurd (Nat.eq_of_beq_eq_true e) (by omega)

theorem nrep_yIdx (i : Fin 6) : NRep 17 Ly0.deg (MS (yIdx (i, true))) (Ly0.yG i) := by
  rcases (by omega : i.val = 5 ∨ i.val < 5) with h | h
  · have e : yIdx (i, true) = 0 := by
      unfold yIdx
      rw [h]
      rfl
    rw [e, h, yG_five']
    exact nrep_A
  · have e : yIdx (i, true) = i.val + 3 := by
      unfold yIdx
      rw [beq_five_false h]
    rw [e]
    exact nrep_y h

theorem yIdx_flip (i : Fin 6) (b : Bool) : yIdx (i, b) = yIdx (i, true) := rfl

theorem nrep_letter_y (l : Fin 6 × Bool) :
    NRep 17 Ly0.deg (MS (yIdx l)) (Ly0.letterG Ly0.yG (letterZ l)) := by
  obtain ⟨i, b⟩ := l
  have hp := nrep_yIdx i
  have hsq : ∀ r < 2 ^ 17, compN 17 [MS (yIdx (i, true)), MS (yIdx (i, true))] r = r := by
    rcases (by omega : i.val = 5 ∨ i.val < 5) with h | h
    · have e : yIdx (i, true) = 0 := by
        unfold yIdx
        rw [h]
        rfl
      rw [e]
      exact pair_id (by decide) (by decide) ly6110_netAA
    · have e : yIdx (i, true) = i.val + 3 := by
        unfold yIdx
        rw [beq_five_false h]
      rw [e]
      exact pair_id (by omega) (by omega) (ly6110_netYY i.val h)
  cases b
  · have e : Ly0.letterG Ly0.yG (letterZ (i, false)) = (Ly0.yG i)⁻¹ := by
      have h1 : ¬ (0 : ℤ) < letterZ (i, false) := by simp [letterZ]
      rw [Ly0.letterG_neg_of _ h1]
      congr 2
      simp [letterZ]
    rw [e, yIdx_flip]
    exact hp.inv deg_le hsq
  · have e : Ly0.letterG Ly0.yG (letterZ (i, true)) = Ly0.yG i := by
      have h1 : (0 : ℤ) < letterZ (i, true) := by simp [letterZ]
      rw [Ly0.letterG_pos _ h1]
      congr 1
      simp [letterZ]
    rw [e]
    exact hp

theorem compN_yNets (r : List (Fin 6 × Bool)) (a : Fin Ly0.deg) :
    compN 17 (yNets MS r) a = (Ly0.wG Ly0.yG (r.map letterZ) a : Nat) := by
  have e : yNets MS r = r.map fun l => MS (yIdx l) := rfl
  rw [e, compN_map (fun l => MS (yIdx l)) (fun l => Ly0.letterG Ly0.yG (letterZ l)) r
    (fun l _ => nrep_letter_y l) a, wG_eq_prod, List.map_map]
  rfl

theorem fix_of_compN {g : Perm (Fin Ly0.deg)} {Ns : List Nat}
    (hg : ∀ a : Fin Ly0.deg, compN 17 Ns a = (g a : Nat)) (b : Fin Ly0.deg)
    (h : Nat.beq (compN 17 Ns b) b = true) : g b = b :=
  Fin.ext ((hg b).symm.trans (Nat.eq_of_beq_eq_true h))

theorem wG_yG_of_baseFix (hbc : RB5Bound) {r : List (Fin 6 × Bool)}
    (h : baseFix (yNets MS r) = true) : Ly0.wG Ly0.yG (r.map letterZ) = 1 := by
  obtain ⟨h0, h31⟩ := andB_true h
  obtain ⟨h3, h1⟩ := andB_true h31
  have hg := compN_yNets r
  refine eq_one_of_fix_base cL_eq_cG dL_eq_dG hbc ?_ (fix_of_compN hg p0 h0)
    (fix_of_compN hg p3 h3) (fix_of_compN hg p1 h1)
  exact Ly0.wG_mem Ly0.B0 Ly0.yG 6 Ly0.yG_mem_B0 _ fun l hl => by
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact Ly0.letterZ_mem l'

theorem cover_baseFix : ∀ r ∈ mclCover, baseFix (yNets MS r) = true := by
  intro r hr
  rw [← List.take_append_drop 87 mclCover, List.mem_append] at hr
  rcases hr with hr | hr
  · exact List.all_eq_true.1 ly6110_cover0 r hr
  · exact List.all_eq_true.1 ly6110_cover1 r hr

theorem coverCheck_true (hbc : RB5Bound) : Ly0.coverCheck = true := by
  unfold Ly0.coverCheck
  refine List.all_eq_true.2 fun r hr => beq_iff_eq.2 ?_
  have hw : ∀ l ∈ r.map letterZ, l ≠ 0 ∧ l.natAbs ≤ 6 := fun l hl => by
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact Ly0.letterZ_mem l'
  have h1 := Ly0.rep_yWord tabCheck_true _ hw
  rw [wG_yG_of_baseFix hbc (cover_baseFix r hr)] at h1
  exact Ly0.tab_eq_of_rep (Ly0.wT_size _ _ _) Ly0.idT_size h1 (Rep.idT Ly0.deg_lt)

end CertificateChecks.KernelLyModel

end
