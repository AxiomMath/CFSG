module

public import CFSG.YGroups.Exact.Y321Inputs
public import Certificates.Kernel.YModel.Basic
public import Certificates.Kernel.YChain.Chain
public import CFSG.Certificates.Kernel.YModel.Y321.Data
import Certificates.Kernel.YChain.Tables.YCh321
import CFSG.Certificates.Kernel.YModel.Y321.Checks

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC CFSG.KC.YModel CFSG.YGroups CFSG.Certificates CFSG.Certificates.KB

set_option maxRecDepth 100000

theorem y321_lines : ∀ c < 7, letOK 6 56 (CFSG.KD.YM321P.F c) (CFSG.KD.YMY321.Nf c) = true ∧
    Nat.beq (lget CFSG.KD.YM321P.El c) 56 = true := by
  intro c hc
  have h : CFSG.KD.YMY321.ch10097let c = true := by
    interval_cases c
    exacts [CFSG.KD.YMY321.ch10097let0, CFSG.KD.YMY321.ch10097let1, CFSG.KD.YMY321.ch10097let2,
      CFSG.KD.YMY321.ch10097let3, CFSG.KD.YMY321.ch10097let4, CFSG.KD.YMY321.ch10097let5,
      CFSG.KD.YMY321.ch10097let6]
  unfold CFSG.KD.YMY321.ch10097let at h
  exact andB_eq_true h

theorem y321_arrays_eq : y321Arrays = linesA (fun _ => 56) 32 (CFSG.KD.YM321P.F) 7 := by
  have h := decBind_perms CFSG.KD.YM321P.ok
  rw [← charsOf_eq, ← CFSG.KD.YM321P.eq] at h
  rw [y321Arrays, h]
  change linesA (lget CFSG.KD.YM321P.El) 32 (CFSG.KD.YM321P.F) 7 = _
  exact linesA_congr fun L hL => Nat.eq_of_beq_eq_true (y321_lines L hL).2

theorem y321_let : ∀ c < 7, letOK 6 56 (CFSG.KD.YM321P.F c) (CFSG.KD.YMY321.Nf c) = true :=
  fun c hc => (y321_lines c hc).1

theorem y321_size : y321Arrays.size = 7 := by
  rw [y321_arrays_eq, size_linesA]

theorem y321_perms : ModelNative.permsOK 56 y321Arrays = true := by
  rw [y321_arrays_eq]
  exact permsOK_of_letOK y321_let

theorem y321_relators : ModelNative.relatorsOK 56 y321Arrays (yRels 3 2 1) = true := by
  rw [y321_arrays_eq]
  exact relatorsOK_of_relsOK y321_let CFSG.KD.YMY321.ch10097rels

theorem y321_W0 : y321Words = linesW (fun L => CFSG.KD.YMY321.WL0 (L - 1)) 32
    (fun L => CFSG.KD.YMY321.WP0 (L - 1)) (0 + 1) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM321C.ok).2
  rw [← charsOf_eq, ← CFSG.KD.YM321C.eq] at h
  rw [y321Words, h]
  rfl

theorem y321_base0 : y321Base = unpackA 6 32 (CFSG.KD.YM321C.F 0) := by
  have h := (decBind_chain (by decide) CFSG.KD.YM321C.ok).1
  rw [← charsOf_eq, ← CFSG.KD.YM321C.eq] at h
  rw [y321Base, h]
  rfl

theorem y321_chain : ModelNative.chainOK 56 y321Arrays y321Words y321Base = true ∧
    ModelNative.chainSizes 56 y321Arrays y321Words y321Base = [56, 27, 16, 10, 6, 2] := by
  have h := chainOK_of_checks (m := 7) (nw := 0) (T := CFSG.KD.YMY321.T0)
    (R := CFSG.KD.YMY321.R0) (M := CFSG.KD.YMY321.M0) (Z := CFSG.KD.YMY321.Z0) (w := 32)
    (WP := CFSG.KD.YMY321.WP0) (WL := CFSG.KD.YMY321.WL0) y321_let y321_W0 y321_base0
    (by intro c hc; interval_cases c <;> rfl)
    (by intro i hi; omega)
    (by
      intro i hi
      interval_cases i
      exacts [CFSG.KD.YMY321.ch10097lev0, CFSG.KD.YMY321.ch10097lev1,
        CFSG.KD.YMY321.ch10097lev2, CFSG.KD.YMY321.ch10097lev3, CFSG.KD.YMY321.ch10097lev4,
        CFSG.KD.YMY321.ch10097lev5])
  rw [y321_arrays_eq]
  exact ⟨h.1, h.2.trans rfl⟩

theorem y321_le : Finite (YGroup 3 2 1) ∧ Nat.card (YGroup 3 2 1) ≤ 2903040 := by
  have := CertificateChecks.KernelYChain.y221.1
  have hm : ∀ w ∈ yRels 2 2 1, w.map (shiftAt 2) ∈ yRels 3 2 1 := by decide
  have t := CertificateChecks.KernelYChain.YCh321.t1
  unfold CFSG.KBRoute.YCh321.T1.ok at t
  have h := CertificateChecks.KernelYChain.card_le_of_table (shiftAt 2) hm t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh321.top
  have h2 := Nat.mul_le_mul_left 56 CertificateChecks.KernelYChain.y221.2
  exact ⟨h.1, h.2.trans (by omega)⟩

end CertificateChecks.KernelYModel

end
