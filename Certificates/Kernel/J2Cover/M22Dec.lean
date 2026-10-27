module

public import Certificates.Kernel.J2Cover.M22Bind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.J2Models
open CFSG.ComponentClassification.J2Cover.Models

theorem fDC_all (a : Nat) (ha : a < 128) : fDC a = true :=
  CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) DCBJ2.all a ha

theorem dc_bounds (a : Nat) (ha : a < 128) : Nat.beq (Nat.shiftRight (DP a) (4725 * 7)) 0 = true ∧
    Nat.beq (Nat.shiftRight (DI a) (4725 * 13)) 0 = true := by
  have h := fDC_all a ha
  unfold fDC at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  exact ⟨h1, ((bAnd_iff _ _).1 h).1⟩

theorem dc_rest (a : Nat) (ha : a < 128) :
    (a = 0 → ∀ i < 4725, pg 7 (mask 7) (DP 0) i = 0 ∧ pg 13 (mask 13) (DI 0) i = i) ∧
    (a ≠ 0 → par a < a ∧ ∀ i < 4725, pg 13 (mask 13) (YI (gen a)) i < 4725 ∧
      pg 7 (mask 7) (DP a) i = mtK (pg 7 (mask 7) (YP (gen a)) i)
        (pg 7 (mask 7) (DP (par a)) (pg 13 (mask 13) (YI (gen a)) i)) ∧
      pg 13 (mask 13) (DI a) i = pg 13 (mask 13) (DI (par a)) (pg 13 (mask 13) (YI (gen a)) i)) := by
  have h := fDC_all a ha
  unfold fDC at h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun h0 i hi => ?_, fun h0 => ?_⟩
  · subst h0
    have h' := allN_spec h i hi
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
  · rw [beq_false h0] at h
    obtain ⟨hp, h⟩ := (bAnd_iff _ _).1 h
    refine ⟨Nat.le_of_ble_eq_true hp, fun i hi => ?_⟩
    have h' := allN_spec h i hi
    rw [strictB_eq', strictB_eq'] at h'
    obtain ⟨h1, h'⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h'
    exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem decompCols_bind : decompCols =
    (Array.ofFn (n := 128) fun a => Array.ofFn (n := 4725) fun i => pg 7 (mask 7) (DP a.val) i.val,
      Array.ofFn (n := 128) fun a => Array.ofFn (n := 4725) fun i => pg 13 (mask 13) (DI a.val) i.val) := by
  rw [decompCols_eq]
  refine decompColsG_sound (P := fun a i => pg 7 (mask 7) (DP a) i)
    (I := fun a i => pg 13 (mask 13) (DI a) i) (fun i hi => (dc_rest 0 (by omega)).1 rfl i hi)
    (fun a ha h1 => ((dc_rest a ha).2 (by omega)).1) (fun a ha h1 i hi => ?_)
    (fun a ha h1 i hi => ?_) (fun a _ => gen_lt a)
  · rw [yDecomp_pt _ i (gen_lt a) hi]
    exact (((dc_rest a ha).2 (by omega)).2 i hi).1
  · obtain ⟨-, h2, h3⟩ := ((dc_rest a ha).2 (by omega)).2 i hi
    rw [yDecomp_pt _ i (gen_lt a) hi]
    refine ⟨?_, h3⟩
    rw [mt_pt]
    exact h2

theorem pT_pt (i a : Nat) : pTab i a = pK i a := by
  unfold pTab pK
  rw [decompCols_bind]
  dsimp only
  by_cases ha : a < 128
  · rw [blt_true ha, getElem!_ofFn' ha]
    by_cases hi : i < 4725
    · rw [getElem!_ofFn' hi]
    · rw [getElem!_neg _ i (by rw [Array.size_ofFn]; exact hi), pg_beyond (dc_bounds a ha).1 (by omega)]
      rfl
  · rw [blt_false ha, getElem!_neg _ a (by rw [Array.size_ofFn]; exact ha)]
    rfl

theorem iT_pt (i a : Nat) : iTab i a = iK i a := by
  unfold iTab iK
  rw [decompCols_bind]
  dsimp only
  by_cases ha : a < 128
  · rw [blt_true ha, getElem!_ofFn' ha]
    by_cases hi : i < 4725
    · rw [getElem!_ofFn' hi]
    · rw [getElem!_neg _ i (by rw [Array.size_ofFn]; exact hi), pg_beyond (dc_bounds a ha).2 (by omega)]
      rfl
  · rw [blt_false ha, getElem!_neg _ a (by rw [Array.size_ofFn]; exact ha)]
    rfl

theorem pT_eq : pTab = pK := funext fun i => funext fun a => pT_pt i a

theorem iT_eq : iTab = iK := funext fun i => funext fun a => iT_pt i a

end CertificateChecks.KernelJ2Cover

end
