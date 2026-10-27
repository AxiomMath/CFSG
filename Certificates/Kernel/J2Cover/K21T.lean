module

public import Certificates.Kernel.J2Cover.K21
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText TxtKernel
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.Kernel

theorem crT_cnt : Nat.beq (prodCnt 315 9 3 CRT.LR CRT.TR (ord4K 315 9)) RT.N = true := by quickRfl

@[expose] noncomputable def fRT (j : Nat) : Bool :=
  repK 315 9 RT.GP RT.GIP 3 RT.CS RT.OFF RT.CI RT.E RT.P RT.L RT.K RT.S RT.SI RT.N 4000 j

#lc_blocks RTB fRT 660 8

theorem crT : crTCheck = true := by
  unfold crTCheck
  rw [Bool.and_eq_true]
  refine ⟨chainCheck_of crT_binds (by norm_num) crT_chain hta hou (fun j hj => ?_) (by quickRfl)
    (by quickRfl) (fun j hj => ?_) (fun j hj => ?_) (by quickRfl) (by quickRfl) (fun j hj => ?_), ?_⟩
  · interval_cases j <;> quickRfl
  · interval_cases j <;> quickRfl
  · interval_cases j <;> quickRfl
  · interval_cases j <;> quickRfl
  have e0 := bind_txt (P := RT.E (lget RT.OFF 0)) (cs := C.crTReps.c0) rfl rfl (by quickRfl)
    (by quickRfl)
  have e1 := bind_txt (P := RT.E (lget RT.OFF 1)) (cs := C.crTReps.c1) rfl rfl (by quickRfl)
    (by quickRfl)
  have e2 := bind_txt (P := RT.E (lget RT.OFF 2)) (cs := C.crTReps.c2) rfl rfl (by quickRfl)
    (by quickRfl)
  have e3 := bind_txt (P := RT.E (lget RT.OFF 3)) (cs := C.crTReps.c3) rfl rfl (by quickRfl)
    (by quickRfl)
  have er : crTReps = [CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.crTReps.c0),
      CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.crTReps.c1),
      CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.crTReps.c2),
      CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.crTReps.c3)] := by
    rw [← C.crTReps.e0, ← C.crTReps.e1, ← C.crTReps.e2, ← C.crTReps.e3]
    rfl
  have hN : RT.N = 660 := rfl
  refine classCheck_of (k := 3) (GP := RT.GP) (GIP := RT.GIP) (CI := RT.CI) (E := RT.E) (P := RT.P)
    (L := RT.L) (K := RT.K) (Ss := RT.S) (SI := RT.SI) (CS := RT.CS) (OFF := RT.OFF) (N := RT.N)
    crT_binds crT_perm CRT.hl (by norm_num) (fun l hl => ?_) (fun l hl => ?_) (fun l hl => ?_)
    (by rw [er, e0, e1, e2, e3]; rfl) (by quickRfl) (by quickRfl) (Nat.eq_of_beq_eq_true crT_cnt)
    (fun j hj => CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RTB.all j
      (by rw [hN] at hj; exact hj)) rfl (fun i hi => ?_)
  · interval_cases l <;> exact ⟨Nat.eq_of_beq_eq_true (by quickRfl),
      Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · interval_cases l <;> exact ⟨by quickRfl, by quickRfl⟩
  · interval_cases l <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  · change i < 4 at hi
    interval_cases i <;>
      exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem facts10021 : cpACheck = true ∧ crACheck = true ∧ cpTCheck = true ∧ crTCheck = true ∧
    crUCheck = true :=
  ⟨cpA, crA, cpT, crT, crU⟩

end CertificateChecks.KernelJ2Cover

end
