module

public import Certificates.Data.Kernel.Misc.YamakiBicom
public import Certificates.Data.YamakiG3
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KD.YamakiBicom

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KC.Misc.Spec

theorem ch550751_check : bcChk bcGL bcG8 bcB 0 = true := by quickRfl

theorem ch550751_basis : ∀ q ∈ List.zip bcIdx bcB,
    bicomMat (Pi.single q.1.1 (Pi.single q.1.2 1)) =
      (pkMat 6 q.2).submatrix finSumFinEquiv finSumFinEquiv := by
  decide +kernel

theorem ch550751_gens : ∀ q ∈ List.zip bicomLetters bcGL, yamakiMat6 q.1 = pkMat 6 q.2 := by
  decide +kernel

theorem ch550751_g8 : yamakiMat6 8 = pkMat 6 bcG8 := by decide +kernel

theorem ch550751_expand : BicomExpand := by
  unfold BicomExpand
  exact ⟨by decide +kernel, by decide +kernel⟩

end CFSG.KD.YamakiBicom
