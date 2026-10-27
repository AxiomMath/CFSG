module

public import Certificates.Kernel.E27Spor.Fi24OrbChecksA
public import Certificates.Kernel.E27Spor.Fi24OrbChecksB
public import CFSG.Certificates.Kernel.E27Spor.OrbRec
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelE27Spor.Fi24Orb

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.E27Spor CFSG.KS CFSG.KS.E27Lie CFSG.KS.E27Spor
open CFSG.Monster.B.Pinned CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Foote.E27.OrbitF3

#kc_forall_tree orbAll (fun q => ch131300orb q = true) 198
  CertificateChecks.KernelE27Spor.Fi24Orb.ch131300orb

theorem fi24_orbit : (MulAction.orbit (Subgroup.closure {g | g ∈ [Fi24.XU, Fi24.YU]})
    (⟨rowsVec 3 10 Fi24.base⟩ : RowVD 10)).ncard = 12672 := by
  have hb := blk_all (b := 64) (n := 12672) (m := 198) (by norm_num) (by norm_num) orbAll
  have hrows : ∀ (i : ℕ) (h₁ : i < [Fi24.XU, Fi24.YU].length) (h₂ : i < rows.length),
      (([Fi24.XU, Fi24.YU][i] : GL (Fin 10) (ZMod 3)) : Matrix (Fin 10) (Fin 10) (ZMod 3)) =
        rowsMat 3 10 rows[i] := by
    intro i h₁ h₂
    have : i = 0 ∨ i = 1 := by simp at h₁; omega
    rcases this with rfl | rfl <;> rfl
  have hvb : ValidD 10 Fi24.base := ⟨rfl, by decide⟩
  exact ncard_orbit_of_checks (d := 10) (gens := [Fi24.XU, Fi24.YU]) (rows := rows) rfl hrows
    hvb (N := 12672) (C := C) (pp := pp) (pj := pj) (s := sg) (im := im) (by norm_num)
    (fun i hi => ((bAnd_iff _ _).1 (hb i hi)).1)
    (fun i hi => ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (hb i hi)).2).1)
    (fun i hi => ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (hb i hi)).2).2)

end CertificateChecks.KernelE27Spor.Fi24Orb

end
