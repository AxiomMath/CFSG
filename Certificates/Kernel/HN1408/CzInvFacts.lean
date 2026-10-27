
module

public import Certificates.Kernel.HN1408.CzTScan
public import Certificates.Kernel.HN1408.CzInvChk
public import Certificates.Kernel.HN1408.RepWitFacts
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT

#kc_forall_chunks inv_all (fun s => invSl s = true) 20 CFSG.KD.HN1408.ch26771inv.sl 1

@[expose] noncomputable def repE (c : Nat) : Equiv.Perm (Fin 1408) := t0P (fd (R c) 0) * t1P (fd (R c) 1)

theorem cell_ok {i j : Nat} (hi : i < 1280) (hj : j < 24) :
    cellK R (T0 i) (T1 j) (W i) j = true := by
  have hs : i / 64 < 20 := by omega
  have h := inv_all (i / 64) hs
  unfold invSl at h
  have h' := allN_spec h (i % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h'
  unfold rowK at h'
  simp only [strictB_app] at h'
  exact allN_spec h' j hj

theorem ev_mul {i j i' j' x : Nat} (hi : i < 1280) (hj : j < 24) (hi' : i' < 1280) (hj' : j' < 24)
    (hx : x < 1408) :
    pt (T0 i) (pt (T1 j) (pt (T0 i') (pt (T1 j') x))) =
      (((t0P i * t1P j) * (t0P i' * t1P j')) ⟨x, hx⟩).val := by
  rw [ev_eq hi' hj' hx, ev_eq hi hj (Fin.isLt _), Fin.eta]
  rfl

theorem mem_cz (hP : Nat.card ↥P1408 = 177408000) {i j : Nat} (hi : i < 1280) (hj : j < 24) :
    t0P i * t1P j ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  rw [← (czT_eq hP).1]
  exact mul_mem (t0P_spec hi).1 (t1P_spec hj).1

theorem conjK_parts {A B c₁ i' j' : Nat} (h : conjK R A B c₁ i' j' = true) :
    i' < 1280 ∧ j' < 24 ∧ fd (R (Nat.pred c₁)) 0 < 1280 ∧ fd (R (Nat.pred c₁)) 1 < 24 ∧
      cjAt A B (T0 i') (T1 j') (T0 (fd (R (Nat.pred c₁)) 0)) (T1 (fd (R (Nat.pred c₁)) 1)) 0 =
        true ∧
      cjAt A B (T0 i') (T1 j') (T0 (fd (R (Nat.pred c₁)) 0)) (T1 (fd (R (Nat.pred c₁)) 1)) 1 =
        true := by
  unfold conjK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, h⟩ := mkA h
  obtain ⟨e, f⟩ := mkA h
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.blt_eq.mp c, Nat.blt_eq.mp d, e, f⟩

theorem inv_conj (hP : Nat.card ↥P1408 = 177408000) {g : Equiv.Perm (Fin 1408)}
    (hg : g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) (h2 : g * g = 1)
    (h1 : g ≠ 1) :
    ∃ c < 12, fd (R c) 0 < 1280 ∧ fd (R c) 1 < 24 ∧
      ∃ h ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))), g * h = h * repE c := by
  obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hg
  have hc := cell_ok hi hj
  unfold cellK at hc
  simp only [strictB_app] at hc
  have hsq : isBase (pt (T0 i) (pt (T1 j) (pt (T0 i) (pt (T1 j) 0))))
      (pt (T0 i) (pt (T1 j) (pt (T0 i) (pt (T1 j) 1)))) 0 1 = true := by
    unfold isBase
    rw [ev_mul hi hj hi hj (by norm_num), ev_mul hi hj hi hj (by norm_num), h2]
    rfl
  have hne : isBase (pt (T0 i) (pt (T1 j) 0)) (pt (T0 i) (pt (T1 j) 1)) 0 1 = false := by
    refine Bool.eq_false_iff.2 fun hb => h1 ?_
    exact base_eq hP hg (one_mem _) (fun y hy => ev_eq hi hj hy) rfl rfl hb
  rw [hsq, hne] at hc
  rcases mkIf hc with ⟨-, hX⟩ | ⟨hc0, hX⟩
  · exact absurd hX Bool.false_ne_true
  rcases mkIf hX with ⟨-, hX⟩ | ⟨h12, hK⟩
  · exact absurd hX Bool.false_ne_true
  have hc1 : fd (W i) (Nat.mul 3 j) ≠ 0 := fun e => by rw [e] at hc0; exact absurd hc0 (by decide)
  have hc12 : ¬ 12 < fd (W i) (Nat.mul 3 j) := fun e => by
    rw [Nat.blt_eq.mpr e] at h12
    exact absurd h12 (by decide)
  obtain ⟨hi', hj', hq, hq', e0, e1⟩ := conjK_parts hK
  refine ⟨_, by rw [Nat.pred_eq_sub_one]; omega, hq, hq', _, mem_cz hP hi' hj', ?_⟩
  unfold cjAt at e0 e1
  have g0 := Nat.eq_of_beq_eq_true e0
  have g1 := Nat.eq_of_beq_eq_true e1
  rw [ev_mul hi hj hi' hj' (by norm_num), ev_mul hi' hj' hq hq' (by norm_num)] at g0
  rw [ev_mul hi hj hi' hj' (by norm_num), ev_mul hi' hj' hq hq' (by norm_num)] at g1
  exact eq_of_base hP (mul_mem hg (mem_cz hP hi' hj')) (mul_mem (mem_cz hP hi' hj')
    (mem_cz hP hq hq')) (Fin.ext g0) (Fin.ext g1)

end CFSG.KD.HN1408.CzInv

end
