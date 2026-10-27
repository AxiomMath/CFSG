module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Sporadic.HeldB.CertPChainData
public import CFSG.Sporadic.HeldB.CertPFieldsData
meta import CFSG.Sporadic.HeldB.CertPChainData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Mathlib.Data.Fintype.Card

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HeText CFSG.Sporadic.HeldB.heStrongHex

#kmisc_hexflat CertificateChecks.KernelSpor.HeText CFSG.Sporadic.HeldB.heStrongHex 4 8330 14 9

namespace CertificateChecks.KernelSpor.HeText

open CFSG.Sporadic.HeldB CFSG.KS.Raw CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.PairCount

theorem heStrong_eq {j : Nat} (hj : j < 9) : heStrong j = unpack 8330 14 (F j) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound all j hj
  rw [← eq] at h
  exact h

theorem fixP : ∀ j ∈ heStabIdx, pg 14 (mask 14) (F j) 0 = 0 := by
  decide +kernel

theorem moveP : ∀ y < 8330, y = 0 ∨ ∃ j ∈ heStabIdx, pg 14 (mask 14) (F j) y ≠ y := by
  decide +kernel

theorem idx_lt : ∀ j ∈ heStabIdx, j < 9 := by
  decide

theorem facts : (∀ j ∈ heStabIdx, (heStrong j)[0]! = 0) ∧
    (∀ y < 8330, y = 0 ∨ ∃ j ∈ heStabIdx, (heStrong j)[y]! ≠ y) := by
  refine ⟨fun j hj => ?_, fun y hy => ?_⟩
  · rw [heStrong_eq (idx_lt j hj), unpack_get (by decide)]
    exact fixP j hj
  · rcases moveP y hy with h | ⟨j, hj, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨j, hj, ?_⟩
      rw [heStrong_eq (idx_lt j hj), unpack_get hy]
      exact h

end CertificateChecks.KernelSpor.HeText

end
