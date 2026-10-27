module

public import Certificates.Kernel.LocalComp.M12E1.Checks
public import CFSG.Certificates.Kernel.LocalCompPinSound
import all Init.Data.Range.Basic
public import Certificates.Kernel.LocalComp.M12E1.Enum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12E1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.PSL3Four.Native Certificates.CoreE1Perm
open CertificateChecks.KernelLC

theorem k_sng : M12S.ng = 3 := by decide +kernel

theorem k_sbind : ∀ k < 3, (sGens m12E1Data)[k]! = unpack 12 4 (M12S.G k) := by
  intro k hk
  match k, hk with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel

theorem s_pin : enumOK 12 (sGens m12E1Data) (enumBFS 12 (sGens m12E1Data) 27) = true ∧
    (enumBFS 12 (sGens m12E1Data) 27).tabs =
      Array.ofFn (n := M12S.N) fun i => unpack 12 4 (M12S.T i.val) := by
  have hs : (sGens m12E1Data).size = M12S.ng := by rw [k_sng]; decide +kernel
  have hg : ∀ k < M12S.ng, (sGens m12E1Data)[k]! = unpack 12 4 (M12S.G k) := by
    intro k hk
    rw [k_sng] at hk
    exact k_sbind k hk
  exact CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK hs hg M12S.ok (by decide +kernel)

theorem s_tabs : (sEnum m12E1Data).tabs =
    Array.ofFn (n := M12S.N) fun i => unpack 12 4 (M12S.T i.val) := s_pin.2

theorem k_sOK : sOK m12E1Data = true := by
  unfold sOK
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨s_pin.1, ?_⟩, by decide +kernel⟩
  rw [s_tabs]
  decide +kernel

theorem k_zOK : zOK m12E1Data = true := by
  unfold zOK
  rw [s_tabs]
  simp only [central, sGens, Array.contains_eq_any_beq, ← Array.any_toList, ← Array.all_toList,
    Array.toList_ofFn, List.toList_toArray]
  decide +kernel

theorem k_xOK : xOK m12E1Data = true := by
  unfold xOK
  rw [s_tabs]
  simp only [central, sGens, Array.contains_eq_any_beq, ← Array.any_toList, ← Array.all_toList,
    Array.toList_ofFn, List.toList_toArray]
  decide +kernel

theorem m12_e1 : check m12E1Data = true := by
  unfold check
  rw [k_gens, k_sOK, k_zOK, k_xOK, k_len]
  simp only [Bool.true_and]
  unfold allBelow
  rw [List.all_eq_true]
  intro i hi
  have hi4 : i < 4 := by simpa [m12E1Data] using hi
  match i, hi4 with
  | 0, _ => exact k_e0
  | 1, _ => exact k_e1
  | 2, _ => exact k_e2
  | 3, _ => exact k_e3

end CertificateChecks.KernelLC.M12E1

end
