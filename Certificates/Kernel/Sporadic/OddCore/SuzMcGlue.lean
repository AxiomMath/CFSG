module

public import CFSG.Sporadic.SuzRecog.MixedCellCollapse
public import CFSG.Certificates.Kernel.CosetLogSlices
public import CFSG.Certificates.Kernel.CosetLogSound

public section

namespace CertificateChecks.KernelSpor.SuzMc

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.KC.CLog CFSG.Sporadic.SuzRecog.MixedCell

theorem collapse_of_log {nR : ℕ} {cells : List (List ℕ)} {RL RN FD FS FW SD DT N : ℕ → ℕ}
    (hd0 : hdK 6 nR (r32 N 0) (r32 N 2) 336 0 (baseRels ++ cells) [4, 6, 8] RL (r32 RN) FD = true)
    (hd2 : hdK 6 nR (r32 N 0) (r32 N 3) 336 2 (baseRels ++ cells) [4, 6, 8] RL (r32 RN) FD = true)
    (defs : allN (r32 N 1) (defK (r32 N 0) FD DT) = true)
    (nf : Nat.ble (r32 N 0) 120000 = true)
    (hs : ∀ s < 30, factSlK 6 nR (r32 N 1) 336 (r32 N 0) RL (r32 RN) FD FS FW SD DT
      (Nat.mul (nat_lit 4000) s) (nat_lit 4000) = true) :
    collapseMem cells := by
  intro G _ gen hinv hrels z hz
  have hf := clogK_slices (k := 30) (Nat.le_of_ble_eq_true nf) hs
  have hd := fun b hb => CFSG.KS.allN_spec defs b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact clogK_sound hd0 hd hf G gen hinv hrels
  · exact clogK_sound hd2 hd hf G gen hinv hrels

end CertificateChecks.KernelSpor.SuzMc

end
