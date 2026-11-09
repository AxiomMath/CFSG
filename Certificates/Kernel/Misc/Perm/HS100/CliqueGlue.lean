module

public import Certificates.Kernel.Misc.Perm.HS100.CliqueChecks
public import Certificates.Kernel.Misc.Perm.HS100.X3ClsCheck
public import Certificates.Kernel.Misc.Perm.HS100.BaseGlue
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Misc.Perm.HS100.FiveGlue
public import Certificates.Data.Kernel.Misc.PermAdj
public import Certificates.Data.Kernel.Misc.PermClos
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSCliqueData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Clique

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermAdj
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.FiveY
  CFSG.EvenSporadicStandard.HSStd.PumpHS
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.Five (eqA_F hidA pidPP and_of)

theorem cliquePermG : ∀ k < 3, CFSG.KC.Misc.ArrEnum.permB 100 7 (X3Cls.hsW k) = true :=
  fun k hk => allN_spec X3Cls.x3Perm k hk

theorem gens_get : ∀ k < hsGens.size, hsGens[k]! = unpack 100 7 (X3Cls.hsW k) := by
  intro k hk
  have hk3 : k < 3 := hk
  interval_cases k
  · exact hs100Arr_eq 0 (by norm_num)
  · exact hs100Arr_eq 1 (by norm_num)
  · exact hs100Arr_eq 15 (by norm_num)

theorem cA : canonK 100 7 (mask 7) (100 * 7) (HX.F 0) = true :=
  (CFSG.KC.Misc.ArrEnum.pp_of_permB sz (cliquePermG 0 (by norm_num))).1

theorem cB : canonK 100 7 (mask 7) (100 * 7) (HX.F 1) = true :=
  (CFSG.KC.Misc.ArrEnum.pp_of_permB sz (cliquePermG 1 (by norm_num))).1

theorem cU : canonK 100 7 (mask 7) (100 * 7) (HX.F 15) = true :=
  (CFSG.KC.Misc.ArrEnum.pp_of_permB sz (cliquePermG 2 (by norm_num))).1

theorem cX3 : canonK 100 7 (mask 7) (100 * 7) X3 = true :=
  canonK_pcomp (canonK_pcomp cA cU) (canonK_pcomp cA cU)

theorem x3_eq : x3 = unpack 100 7 X3 := by
  rw [x3, hs100Arr_eq 0 (by norm_num), hs100Arr_eq 15 (by norm_num), compA_unpack cA cU,
    compA_unpack (canonK_pcomp cA cU) (canonK_pcomp cA cU)]
  rfl

theorem validG {k : ℕ} (hk : k < 3) : validA 100 hsGens[k]! = true := by
  rw [gens_get k hk]
  exact validA_unpack (cliquePermG k hk)

theorem x3_valid : validA 100 x3 = true := by
  have ra := rep_of_validA (validG (k := 0) (by norm_num))
  have ru := rep_of_validA (validG (k := 2) (by norm_num))
  exact CFSG.RankThree.Native.F2.validA_of_rep (rep_compA (rep_compA ra ru) (rep_compA ra ru))

theorem involA_eq {p : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true) :
    involA (unpack 100 7 p) = invoK 100 7 p := by
  rw [involA, compA_unpack hp hp, hidA, eqA_F (canonK_pcomp hp hp) pidPP.1, eqA_F hp pidPP.1, invoK,
    Bool.and_comm]

theorem adjA_eq {p q : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true)
    (hq : canonK 100 7 (mask 7) (100 * 7) q = true) :
    adjA (unpack 100 7 p) (unpack 100 7 q) = adjK 100 7 p q := by
  rw [adjA, compA_unpack hp hq, involA_eq (canonK_pcomp hp hq), adjK]

theorem fixedA_eq (p : ℕ) : fixedA (unpack 100 7 p) = CFSG.KC.PermAdj.fixedK 100 7 p := by
  rw [fixedA, CFSG.KC.PermAdj.fixedK, CFSG.KC.Misc.ArrEnum.anyNP_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq, Nat.beq_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [unpack_get' hi] at h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [unpack_get' hi]⟩

end CertificateChecks.KernelMisc.HS100.Clique

end
