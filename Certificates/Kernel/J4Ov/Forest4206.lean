module

public import Certificates.Kernel.J4Ov.Defs4206
public import CFSG.Certificates.Kernel.J4Q.RunsSound
public import Certificates.Kernel.J4Q.LocVec
import Certificates.Kernel.J4Ov.Dist4206
import Certificates.Kernel.J4Ov.TreeA4206
import Certificates.Kernel.J4Ov.TreeB4206
public import CFSG.Certificates.Kernel.J4Q.RepVOrb

public section

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KC.LQT.Syl CFSG.KD.J4Ov CertificateChecks.KernelJ4Q
open CFSG.KD.J4Q (c rm one A B L0 L1 L2 U0 mkKM_0 mkKM_1 mkKM_2 mkKM_3)

theorem map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (l.getD · d) = l := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

theorem flatten_map_perm {f g : Nat → List Nat} : ∀ (l : List Nat), (∀ t ∈ l, (f t).Perm (g t)) →
    (l.map f).flatten.Perm (l.map g).flatten
  | [], _ => List.Perm.refl _
  | t :: l, h => by
    rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons]
    exact (h t List.mem_cons_self).append
      (flatten_map_perm l fun s hs => h s (List.mem_cons_of_mem _ hs))

theorem shape_t {t : Nat} (ht : t < 49) : (chT t).length ≤ 8 ∧
    (PP.getD t []).length = (chT t).length ∧ (SC.getD t []).length = (chT t).length + 1 ∧
    ∀ i, i + 1 < (chT t).length → ((chT t).getD i []).length = 1024 := by
  have h := shape4206_ok
  unfold shape4206 at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, -, -, h⟩ := h
  have h := allR_spec h t ht
  simp only [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, -, h5⟩ := h
  exact ⟨h1, h2, h3, fun i hi => Nat.eq_of_beq_eq_true (allR_spec h5 i (by rw [Nat.sub_eq]; omega))⟩

theorem letters_eq {g : Nat} (hg : g < R.length) : R.getD g [] = rowsOfJ rm (getN one letMs g) := by
  have h := letters4206_ok
  unfold lettersK at h
  rw [andB_eq, Bool.and_eq_true] at h
  have h4 : R.length = 4 := Nat.eq_of_beq_eq_true h.1
  exact eqLK_spec (allR_spec h.2 g (by omega))

theorem R_length : R.length = 4 := by
  have h := letters4206_ok
  unfold lettersK at h
  rw [andB_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem tree4206 {t : Nat} (ht : t < 49) : ∀ k, 0 < k → k < (ptsT t).length →
    ∃ p < k, ∃ g < 4, vecJ rm ((ptsT t).getD p 0) (getN one letMs g) = (ptsT t).getD k 0 := by
  obtain ⟨h8, -, -, hB⟩ := shape_t ht
  have hlen : (chT t).flatten.length + 1 = (ptsT t).length := by
    unfold ptsT vptsK
    rw [List.length_cons, List.length_map]
  have htr : ∀ i < (chT t).length, vtChunkK rm R (vptsK rm (RT.getD t 0) (chT t).flatten)
      ((chT t).getD i []) ((PP.getD t []).getD i 0) (1 + 1024 * i) = true := by
    intro i hi
    have key : tr4206 (8 * t + i) = true := by
      by_cases h28 : t < 28
      · have hA : ∀ g < 224, tr4206 g = true := ch4206TA.all
        exact hA (8 * t + i) (by omega)
      · have hB' : ∀ g < 168, tr4206B g = true := ch4206TB.all
        have h := hB' (8 * t + i - 224) (by omega)
        unfold tr4206B at h
        rwa [Nat.sub_add_cancel (by omega)] at h
    have e1 : (8 * t + i) / 8 = t := by omega
    have e2 : (8 * t + i) % 8 = i := by omega
    unfold tr4206 trTI ptsT at key
    rwa [e1, e2] at key
  intro k hk0 hk
  obtain ⟨h1, h2, h3⟩ := vtChunks_sound hlen hB htr k hk0 hk
  refine ⟨_, h1, _, R_length ▸ h2, ?_⟩
  rw [letters_eq h2, vecLJ_rowsOfJ] at h3
  exact h3

theorem roots4206 {t : Nat} (ht : t < 49) : RT.getD t 0 = pathVK rm one [L0, L1, L2] (W.getD t [])
    (pathVK rm one [A, B] (KP.getD (LS.getD t 0 - 5) []) R0) :=
  Nat.eq_of_beq_eq_true (allR_spec roots4206_ok t ht)

theorem LS_getD {t : Nat} (ht : t < 49) : LS.getD t 0 = if t < 28 then 5 else 6 := by
  have h := shape4206_ok
  unfold shape4206 at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, -, -, h⟩ := h
  have h := allR_spec h t ht
  simp only [andB_eq, Bool.and_eq_true] at h
  have h4 := Nat.eq_of_beq_eq_true h.2.2.2.1
  rw [h4]
  by_cases h28 : t < 28
  · have hb : Nat.blt t 28 = true := by
      rw [Nat.blt_eq]
      exact h28
    rw [if_pos h28, hb]
  · have hb : Nat.blt t 28 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      exact h28
    rw [if_neg h28, hb]

theorem sc_perm {t : Nat} (ht : t < 49) : (SC.getD t []).flatten.Perm (ptsT t) := by
  obtain ⟨h8, -, hsc, -⟩ := shape_t ht
  have hso : ∀ i < (chT t).length + 1, (SC.getD t []).getD i [] = sortN (pcT t i) := by
    intro i hi
    have hS : ∀ g < 441, so4206 g = true := ch4206S.all
    have h := hS (9 * t + i) (by omega)
    have e1 : (9 * t + i) / 9 = t := by omega
    have e2 : (9 * t + i) % 9 = i := by omega
    unfold so4206 at h
    rw [e1, e2] at h
    exact (eqLK_spec h).symm
  have hpc : ((List.range ((chT t).length + 1)).map (pcT t)).flatten = ptsT t := by
    have h1 : (List.range (chT t).length).map (fun j => pcT t (j + 1)) =
        (chT t).map (List.map fun e => Nat.land e rm) := by
      conv_rhs => rw [← map_getD_range (chT t) []]
      rw [List.map_map]
      rfl
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.flatten_cons]
    change [RT.getD t 0] ++ ((List.range (chT t).length).map (fun j => pcT t (j + 1))).flatten = _
    rw [h1, ← List.map_flatten]
    rfl
  have hS : SC.getD t [] =
      (List.range ((chT t).length + 1)).map fun i => (SC.getD t []).getD i [] := by
    rw [← hsc]
    exact (map_getD_range _ _).symm
  rw [hS, ← hpc]
  exact flatten_map_perm _ fun i hi => by
    have h := sortN_perm' (pcT t i)
    rwa [← hso i (List.mem_range.1 hi)] at h

theorem nodup4206 {lo n cap : Nat} (hn : lo + n ≤ 49) (h : distK lo n cap = true) :
    ((List.range' lo n).map ptsT).flatten.Nodup ∧
      ((List.range' lo n).map ptsT).flatten.length = cap := by
  unfold distK at h
  rw [andB_eq, Bool.and_eq_true] at h
  have hflat : (runsK lo n).flatten =
      ((List.range' lo n).map fun t => (SC.getD t []).flatten).flatten := by
    unfold runsK
    rw [List.flatten_flatten, List.map_map]
    rfl
  have hp : (runsK lo n).flatten.Perm ((List.range' lo n).map ptsT).flatten := by
    rw [hflat]
    exact flatten_map_perm _ fun t ht => sc_perm (by rw [List.mem_range'_1] at ht; omega)
  exact ⟨(sincK_nodup h.1).perm ((mergeRunsK_perm _).trans hp),
    hp.length_eq.symm.trans (Nat.eq_of_beq_eq_true h.2)⟩

theorem forest5_4206 : ((List.range' 0 28).map ptsT).flatten.Nodup ∧
    ((List.range' 0 28).map ptsT).flatten.length = 15180 :=
  nodup4206 (by decide) dist5_4206

theorem forest6_4206 : ((List.range' 28 21).map ptsT).flatten.Nodup ∧
    ((List.range' 28 21).map ptsT).flatten.length = 28336 :=
  nodup4206 (by decide) dist6_4206

end CertificateChecks.KernelJ4Ov

end
