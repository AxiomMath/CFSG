module

public import Certificates.Kernel.E27Spor.MOrbSlp
public import Certificates.Kernel.E27Spor.MOrbChecksA
public import Certificates.Kernel.E27Spor.MOrbChecksB
public import Certificates.Kernel.E27Spor.MOrbChecksC
public import CFSG.Certificates.Kernel.E27Spor.SlpRec
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelE27Spor.MOrb

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.E27Spor CFSG.KS CFSG.KS.E27Lie CFSG.KS.E27Spor
open CFSG.Monster.B.Pinned CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Foote.E27.OrbitF3

#kc_forall_tree slpAll (fun q => ch131302slp q = true) 23
  CertificateChecks.KernelE27Spor.MOrb.ch131302slp

#kc_forall_tree orbAll (fun q => ch131302orb q = true) 81
  CertificateChecks.KernelE27Spor.MOrb.ch131302orb

theorem base_valid : ∀ k < 4, ∀ r < 12, ValidD 12 (nthR (nthM base k) r) := by
  simp only [ValidD]
  decide +kernel

theorem base_length : ∀ k < 4, (nthM base k).length = 12 := by decide +kernel

theorem base_mem : ∀ k < 4, ∃ g ∈ MAct.K,
    (g : Matrix (Fin 12) (Fin 12) (ZMod 3)) = rowsMat 3 12 (nthM base k) := by
  intro k hk
  have hX : MAct.XU ∈ MAct.K := Subgroup.subset_closure (by simp)
  have hY : MAct.YU ∈ MAct.K := Subgroup.subset_closure (by simp)
  interval_cases k
  · exact ⟨MAct.XU, hX, rfl⟩
  · exact ⟨MAct.YU, hY, rfl⟩
  · exact ⟨MAct.XU⁻¹, inv_mem hX, rfl⟩
  · exact ⟨MAct.YU⁻¹, inv_mem hY, rfl⟩

theorem outs_lt : OO 0 < 184 ∧ OO 1 < 184 ∧ OO 2 < 184 := by decide +kernel

theorem three_pow_dvd : 3 ^ 7 ∣ Nat.card MAct.K := by
  have hslp := slp_mem (K := MAct.K) (base := base) (nb := 4) (R := RR) (A := AA) (B := BB)
    (n := 184) (fun k hk => ⟨base_length k hk, base_valid k hk, base_mem k hk⟩)
    (blk_all (b := 8) (n := 184) (m := 23) (by norm_num) (by norm_num) slpAll)
  obtain ⟨g0, hg0, e0⟩ := hslp _ outs_lt.1
  obtain ⟨g1, hg1, e1⟩ := hslp _ outs_lt.2.1
  obtain ⟨g2, hg2, e2⟩ := hslp _ outs_lt.2.2
  have hb := blk_all (b := 27) (n := 2187) (m := 81) (by norm_num) (by norm_num) orbAll
  have hgr : ∀ (i : ℕ) (h₁ : i < [g0, g1, g2].length) (h₂ : i < hrows.length),
      (([g0, g1, g2][i] : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) =
        rowsMat 3 12 hrows[i] := by
    intro i h₁ h₂
    have : i = 0 ∨ i = 1 ∨ i = 2 := by simp at h₁; omega
    rcases this with rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2
  have hvb : ValidD 12 MAct.base := ⟨rfl, by decide⟩
  have horb := ncard_orbit_of_checks (d := 12) (gens := [g0, g1, g2]) (rows := hrows) rfl hgr
    hvb (N := 2187) (C := C) (pp := pp) (pj := pj) (s := sg) (im := im) (by norm_num)
    (fun i hi => ((bAnd_iff _ _).1 (hb i hi)).1)
    (fun i hi => ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (hb i hi)).2).1)
    (fun i hi => ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (hb i hi)).2).2)
  set H : Subgroup (GL (Fin 12) (ZMod 3)) := Subgroup.closure {g | g ∈ [g0, g1, g2]} with hH
  have hHK : H ≤ MAct.K := by
    rw [hH, Subgroup.closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
    rcases hg with rfl | rfl | rfl
    · exact hg0
    · exact hg1
    · exact hg2
  have hcard := card_eq_mul_card_stabilizer H (⟨rowsVec 3 12 MAct.base⟩ : RowVD 12)
  rw [horb] at hcard
  have h3 : 3 ^ 7 ∣ Nat.card H := by
    rw [hcard]
    exact Dvd.dvd.mul_left (by norm_num : (3 : ℕ) ^ 7 ∣ 2187) _
  exact h3.trans (Subgroup.card_dvd_of_le hHK)

end CertificateChecks.KernelE27Spor.MOrb

end
