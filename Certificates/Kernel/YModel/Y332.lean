module

public import CFSG.Sporadic.Recognition.Fi22MultiplierInputs
public import CFSG.YGroups.Exact.Y332Inputs
public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.YModel.Y332.Data
import CFSG.Certificates.Kernel.YModel.Y332.Checks

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel CFSG.YGroups CFSG.Sporadic.Recognition.Fi22Multiplier CFSG.Monster.B.Co2.Native

set_option maxRecDepth 100000

theorem y332_letChk : ∀ c < 9, CFSG.KD.YMY332.letChk c = true := by
  intro c hc
  interval_cases c
  exacts [CFSG.KD.YMY332.letChk0, CFSG.KD.YMY332.letChk1, CFSG.KD.YMY332.letChk2,
    CFSG.KD.YMY332.letChk3, CFSG.KD.YMY332.letChk4, CFSG.KD.YMY332.letChk5, CFSG.KD.YMY332.letChk6,
    CFSG.KD.YMY332.letChk7, CFSG.KD.YMY332.letChk8]

theorem y332_lines : ∀ c < 9, Nat.blt (CFSG.KD.YM332P.F c) (Nat.shiftLeft 1 (32 * 28160)) = true ∧
    letOK 15 28162 (signExt 28160 (CFSG.KD.YM332P.F c)) (CFSG.KD.YMY332.Nf c) = true ∧
    Nat.beq (lget CFSG.KD.YM332P.El c) 28160 = true := by
  intro c hc
  have h := y332_letChk c hc
  unfold CFSG.KD.YMY332.letChk at h
  obtain ⟨h1, h2⟩ := andB_eq_true h
  exact ⟨h1, andB_eq_true h2⟩

theorem y332_arrays_eq :
    y332Arrays = linesA (fun _ => 28162) 32 (fun c => signExt 28160 (CFSG.KD.YM332P.F c)) 9 := by
  have h := decBind_perms CFSG.KD.YM332P.ok
  rw [← charsOf_eq, ← CFSG.KD.YM332P.eq] at h
  rw [y332Arrays, h]
  change ModelNative.withSign (linesA (lget CFSG.KD.YM332P.El) 32 (CFSG.KD.YM332P.F) 9) = _
  rw [linesA_congr (n' := fun _ => 28160) (fun L hL => Nat.eq_of_beq_eq_true (y332_lines L hL).2.2)]
  exact withSign_linesA (n := 28160) (m := 9) (fun c hc => lt_of_blt (y332_lines c hc).1)
    (by norm_num)

theorem y332_let : ∀ c < 9, letOK 15 28162 ((fun c => signExt 28160 (CFSG.KD.YM332P.F c)) c)
    (CFSG.KD.YMY332.Nf c) = true :=
  fun c hc => (y332_lines c hc).2.1

open CFSG.YGroups CFSG.Sporadic.Recognition.Fi22Multiplier CFSG.Monster.B.Co2.Native in
theorem c24050 :
    (eqA 28162
      (ModelNative.evalW 28162 y332Arrays
        (List.replicate 3 ((List.replicate 5 (spiderWord 3 3)).flatten ++ [0])).flatten)
      (idA 28162) = true)
    ∧ (eqA 28162 (ModelNative.evalW 28162 y332Arrays (y332Conj.reverse ++ [0, 3, 8] ++ y332Conj))
      (ModelNative.evalW 28162 y332Arrays ([3, 4, 6, 8] ++ f332Word)) = true)
    ∧ (eqA 28162 (ModelNative.evalW 28162 y332Arrays f332Word) (idA 28162) = false) := by
  have e : idA 28162 = ModelNative.evalW 28162 y332Arrays [] := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, y332_arrays_eq, eqA_of_weqK _ _ y332_let]
    exact CFSG.KD.YMY332.w_spider
  · rw [y332_arrays_eq, eqA_of_weqK _ _ y332_let]
    exact CFSG.KD.YMY332.w_conj
  · rw [e, y332_arrays_eq, eqA_of_weqK _ _ y332_let]
    have h := CFSG.KD.YMY332.w_fne
    simp only [Bool.not_eq_true'] at h
    exact h

open CFSG.YGroups CFSG.Sporadic.Recognition.Fi22Multiplier CFSG.Monster.B.Co2.Native in
theorem c291380 :
    (∀ c < 9,
      eqA 28162 (ModelNative.evalW 28162 y332Arrays (f332Word ++ [c]))
        (ModelNative.evalW 28162 y332Arrays ([c] ++ f332Word)) = true)
    ∧ (eqA 28162 (ModelNative.evalW 28162 y332Arrays (f332Word ++ f332Word)) (idA 28162) = true) := by
  have e : idA 28162 = ModelNative.evalW 28162 y332Arrays [] := rfl
  refine ⟨fun c hc => ?_, ?_⟩
  · rw [y332_arrays_eq, eqA_of_weqK _ _ y332_let]
    have h : ∀ c < 9, CFSG.KD.YMY332.comChk c = true := by
      intro c hc
      interval_cases c
      exacts [CFSG.KD.YMY332.comChk0, CFSG.KD.YMY332.comChk1, CFSG.KD.YMY332.comChk2,
        CFSG.KD.YMY332.comChk3, CFSG.KD.YMY332.comChk4, CFSG.KD.YMY332.comChk5,
        CFSG.KD.YMY332.comChk6, CFSG.KD.YMY332.comChk7, CFSG.KD.YMY332.comChk8]
    exact h c hc
  · rw [e, y332_arrays_eq, eqA_of_weqK _ _ y332_let]
    exact CFSG.KD.YMY332.w_fsq

end CertificateChecks.KernelYModel

end
