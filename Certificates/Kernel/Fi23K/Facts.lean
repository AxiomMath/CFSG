module

public import CFSG.Certificates.Kernel.Fi23K.EqSound
public import Certificates.Kernel.Fi23K.ChkDefs
import Certificates.Kernel.Fi23K.Rel0
import Certificates.Kernel.Fi23K.Rel1
import Certificates.Kernel.Fi23K.Surj0
import Certificates.Kernel.Fi23K.Surj1
import Certificates.Kernel.Fi23K.Surj2
import Certificates.Kernel.Fi23K.Surj3
import Certificates.Kernel.Fi23K.Chain0
import Certificates.Kernel.Fi23K.Chain1
import Certificates.Kernel.Fi23K.Chain2
import Certificates.Kernel.Fi23K.Chain3
import Certificates.Kernel.Fi23K.Misc
import Certificates.Kernel.Sporadic.ON.Gen
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

#kon_join CFSG.KD.Fi23K.relAll CFSG.KD.Fi23K.relSl 16
#kon_join CFSG.KD.Fi23K.surjAll CFSG.KD.Fi23K.surjSl 31
#kon_join CFSG.KD.Fi23K.chainAll CFSG.KD.Fi23K.chainSl 31
#kon_join CFSG.KD.Fi23K.miscAll CFSG.KD.Fi23K.miscSl 8

namespace CFSG.KD.Fi23K

open CFSG.KC.Fi23K

theorem fam {k0 nk w s : Nat} (h : eqS k0 nk (s * w) w = true) {k x : Nat} (hk1 : k0 ≤ k)
    (hk2 : k < k0 + nk) (hx : x / w = s) (hw : 0 < w) (hx' : x < 31671) :
    EqHolds G (EL k) (ER k) x := by
  refine eqSl_spec h k hk1 hk2 x ?_ ?_ hx'
  · rw [← hx]
    exact Nat.div_mul_le_self x w
  · rw [← hx]
    exact Nat.lt_div_mul_add hw

theorem eq_all : ∀ k < 150, ∀ x < 31671, EqHolds G (EL k) (ER k) x := by
  intro k hk x hx
  rcases (by omega : k < 65 ∨ (65 ≤ k ∧ k < 96) ∨ (96 ≤ k ∧ k < 136) ∨ 136 ≤ k) with
    h | h | h | h
  · exact fam (w := 2048) (relAll (x / 2048) (by change x / 2048 < 16; omega)) (Nat.zero_le k)
      (by change k < 0 + 65; omega) rfl (by norm_num) hx
  · exact fam (w := 1024) (surjAll (x / 1024) (by change x / 1024 < 31; omega)) h.1
      (by change k < 65 + 31; omega) rfl (by norm_num) hx
  · exact fam (w := 1024) (chainAll (x / 1024) (by change x / 1024 < 31; omega)) h.1
      (by change k < 96 + 40; omega) rfl (by norm_num) hx
  · exact fam (w := 4096) (miscAll (x / 4096) (by change x / 4096 < 8; omega)) h
      (by change k < 136 + 14; omega) rfl (by norm_num) hx

end CFSG.KD.Fi23K

end
