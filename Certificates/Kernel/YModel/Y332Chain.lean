module

public import Certificates.Kernel.YModel.Y332
public import CFSG.Certificates.Kernel.YModel.Y332.Chain
import CFSG.Certificates.Kernel.YModel.Y332.ChainChecks
import CFSG.Certificates.Kernel.YModel.Y332.RelChecks

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel CFSG.YGroups

set_option maxRecDepth 100000

theorem y332_size : y332Arrays.size = 9 := by
  rw [y332_arrays_eq, size_linesA]

theorem y332_perms : ModelNative.permsOK 28162 y332Arrays = true := by
  rw [y332_arrays_eq]
  exact permsOK_of_letOK y332_let

theorem y332_relators : ModelNative.relatorsOK 28162 y332Arrays (yRels 3 3 2) = true := by
  rw [y332_arrays_eq]
  exact relatorsOK_of_relsOK y332_let CFSG.KD.YMY332.ch10099rels

theorem y332_W0 : y332Words = linesW (fun L => CFSG.KD.YMY332.WL0 (L - 1)) 32
    (fun L => CFSG.KD.YMY332.WP0 (L - 1)) (12 + 1) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM332C.ok).2
  rw [← charsOf_eq, ← CFSG.KD.YM332C.eq] at h
  rw [y332Words, h]
  rfl

theorem y332_base0 : y332Base = unpackA 9 32 (CFSG.KD.YM332C.F 0) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM332C.ok).1
  rw [← charsOf_eq, ← CFSG.KD.YM332C.eq] at h
  rw [y332Base, h]
  rfl

theorem y332_chain : ModelNative.chainOK 28162 y332Arrays y332Words y332Base = true ∧
    ModelNative.chainSizes 28162 y332Arrays y332Words y332Base =
      [2, 28160, 3159, 288, 35, 12, 3, 2, 2] := by
  have h := chainOK_of_checks (m := 9) (nw := 12) (T := CFSG.KD.YMY332.T0)
    (R := CFSG.KD.YMY332.R0) (M := CFSG.KD.YMY332.M0) (Z := CFSG.KD.YMY332.Z0) (w := 32)
    (WP := CFSG.KD.YMY332.WP0) (WL := CFSG.KD.YMY332.WL0) y332_let y332_W0 y332_base0
    (by intro c hc; interval_cases c <;> rfl)
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY332.ch10099word0, CFSG.KD.YMY332.ch10099word1,
        CFSG.KD.YMY332.ch10099word2, CFSG.KD.YMY332.ch10099word3, CFSG.KD.YMY332.ch10099word4,
        CFSG.KD.YMY332.ch10099word5, CFSG.KD.YMY332.ch10099word6, CFSG.KD.YMY332.ch10099word7,
        CFSG.KD.YMY332.ch10099word8, CFSG.KD.YMY332.ch10099word9, CFSG.KD.YMY332.ch10099word10,
        CFSG.KD.YMY332.ch10099word11])
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY332.ch10099lev0, CFSG.KD.YMY332.ch10099lev1, CFSG.KD.YMY332.ch10099lev2,
        CFSG.KD.YMY332.ch10099lev3, CFSG.KD.YMY332.ch10099lev4, CFSG.KD.YMY332.ch10099lev5,
        CFSG.KD.YMY332.ch10099lev6, CFSG.KD.YMY332.ch10099lev7, CFSG.KD.YMY332.ch10099lev8])
  rw [y332_arrays_eq]
  exact ⟨h.1, h.2.trans rfl⟩

end CertificateChecks.KernelYModel

end
