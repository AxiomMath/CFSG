module

public import Certificates.Kernel.J2Cover.K21T
public import CFSG.Certificates.Kernel.J2CoverSound
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

theorem classCheck_ofE {S : Array (Array Nat)} {k : Nat} {base : Array Nat}
    {reps : List (Array Nat)} {sizes : List Nat} {kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    (hb : Binds 315 9 PS kS nb BP S base)
    (hp : allN kS (fun j => permOK 315 9 (mask 9) (315 * 9) (PS j) (PSI j)) = true)
    (hl : LevelsOK 315 9 PS PSI LR TR TRI kS nb BP) (hk : k ≤ kS)
    {GP GIP CI E P L K Ss SI : Nat → Nat} {CS OFF : List Nat} {N : Nat}
    (hGP : ∀ l < k, GP l = PS l ∧ GIP l = PSI l)
    (hgc : ∀ l < k, canonK 315 9 (mask 9) (315 * 9) (GP l) = true ∧
      canonK 315 9 (mask 9) (315 * 9) (GIP l) = true)
    (hinv : ∀ l < k, pcomp 315 9 (mask 9) (GP l) (GIP l) = pidn 315 9)
    (hreps : reps = (List.range CS.length).map fun i => unpack 315 9 (E (lget OFF i)))
    (hoff : offOK CS OFF N = true) (hpos : allL (fun c => Nat.blt 0 c) CS = true)
    (hcnt : prodCnt 315 9 nb LR TR (ord4K 315 9) = N)
    (h : ∀ j < N, repK 315 9 GP GIP k CS OFF CI E P L K Ss SI N 4000 j = true)
    (hsz : CS = sizes)
    (hrep : ∀ i < CS.length, RepFacts nb BP LR TRI (E (lget OFF i))) :
    classCheck S k base reps sizes = true := by
  have hg : (genTbls S k).size = k ∧ (genInvTbls S k).size = k ∧ ∀ l < k,
      (genTbls S k)[l]! = arrTable 315 (unpack 315 9 (GP l)) ∧
        (genInvTbls S k)[l]! = arrTable 315 (unpack 315 9 (GIP l)) := by
    refine ⟨by simp [genTbls], by simp [genInvTbls], fun l hl => ⟨?_, ?_⟩⟩
    · rw [genTbls, getElem!_pos _ l (by simp [hl])]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      rw [hb.2.2.2.2.1 l (by omega), (hGP l hl).1]
    · rw [genInvTbls, getElem!_pos _ l (by simp [hl])]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      rw [hb.2.2.2.2.1 l (by omega), (invEqK_sound (allN_spec hp l (by omega))).1, (hGP l hl).2]
  have hreps' : reps.map (arrTable 315) =
      (List.range CS.length).map fun i => arrTable 315 (unpack 315 9 (E (lget OFF i))) := by
    rw [hreps, List.map_map, Function.comp_def]
  have hX : (fourTables S base).length = N := by
    unfold fourTables
    rw [prodCnt_sound hb hp hl (fun X hX => CFSG.KC.J2Cover.ord4_unpack hX)]
    exact hcnt
  have h1 := repsOK_sound hg hgc hreps' hoff hpos hX h
  have h2 := repSizes_sound hg hgc hreps' hoff hpos h
  have h3 := CFSG.KC.J2Cover.closedOK_sound hg hgc hinv hoff hpos h rfl
  unfold classCheck
  rw [h1, h2, ← hsz, beq_self_eq_true, Bool.true_and, Bool.true_and, List.all_eq_true]
  intro r hr
  rw [hreps] at hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
  have hi' := List.mem_range.1 hi
  obtain ⟨hinvR, hcan, hord, hz, hs⟩ := hrep i hi'
  obtain ⟨e1, e2⟩ := invEqK_sound hinvR
  unfold closureEntries
  rw [e1, e2, CFSG.KC.J2Cover.ord4_unpack hcan, hord,
    siftK_soundR hb hp hl rfl (Nat.eq_of_beq_eq_true hz) (range_of_canonK hcan) hs,
    h3 i hi']
  rfl

theorem cpAE : cpACheck = true := by
  unfold cpACheck
  refine classCheck_ofE (k := 2) (GP := C2B.S) (GIP := C2B.SI) (CI := fun _ => 0)
    (E := fun _ => 0) (P := fun _ => 0) (L := fun _ => 0) (K := fun _ => 0) (Ss := fun _ => 0)
    (SI := fun _ => 0) (CS := []) (OFF := []) (N := 0) c2B_binds c2B_perm C2B.hl (by norm_num)
    (fun _ _ => ⟨rfl, rfl⟩) (fun l hl => ?_) (fun l hl => ?_) rfl (by quickRfl) rfl
    (Nat.eq_of_beq_eq_true cpA_cnt) (fun j hj => absurd hj (Nat.not_lt_zero j)) rfl
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  · interval_cases l <;> exact ⟨by quickRfl, by quickRfl⟩
  · interval_cases l <;> exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem crAE : crACheck = true := by
  unfold crACheck
  rw [Bool.and_eq_true]
  refine ⟨chainCheck_of crA_binds (by norm_num) crA_chain ha hou (fun j hj => ?_) (by quickRfl)
    (by quickRfl) (fun j hj => ?_) (fun j hj => ?_) (by quickRfl) (by quickRfl) (fun j hj => ?_), ?_⟩
  · interval_cases j <;> quickRfl
  · interval_cases j <;> quickRfl
  · interval_cases j <;> quickRfl
  · interval_cases j <;> quickRfl
  have e0 := bind_txt (P := RA.E (lget RA.OFF 0)) (cs := C.crAReps.c0) rfl rfl (by quickRfl)
    (by quickRfl)
  have e1 := bind_txt (P := RA.E (lget RA.OFF 1)) (cs := C.crAReps.c1) rfl rfl (by quickRfl)
    (by quickRfl)
  have e2 := bind_txt (P := RA.E (lget RA.OFF 2)) (cs := C.crAReps.c2) rfl rfl (by quickRfl)
    (by quickRfl)
  have er : crAReps = [CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.crAReps.c0),
      CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.crAReps.c1),
      CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.crAReps.c2)] := by
    rw [← C.crAReps.e0, ← C.crAReps.e1, ← C.crAReps.e2]
    rfl
  have hN : RA.N = 140 := rfl
  refine classCheck_ofE (k := 3) (GP := RA.GP) (GIP := RA.GIP) (CI := RA.CI) (E := RA.E)
    (P := RA.P) (L := RA.L) (K := RA.K) (Ss := RA.S) (SI := RA.SI) (CS := RA.CS) (OFF := RA.OFF)
    (N := RA.N) crA_binds crA_perm CRA.hl (by norm_num) (fun l hl => ?_) (fun l hl => ?_)
    (fun l hl => ?_) (by rw [er, e0, e1, e2]; rfl) (by quickRfl) (by quickRfl)
    (Nat.eq_of_beq_eq_true crA_cnt)
    (fun j hj => CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RAB.all j
      (by rw [hN] at hj; exact hj)) rfl (fun i hi => ?_)
  · interval_cases l <;> exact ⟨Nat.eq_of_beq_eq_true (by quickRfl),
      Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · interval_cases l <;> exact ⟨by quickRfl, by quickRfl⟩
  · interval_cases l <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  · change i < 3 at hi
    interval_cases i <;>
      exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem cpTE : cpTCheck = true := by
  unfold cpTCheck
  have e0 := bind_txt (P := RPT.E (lget RPT.OFF 0)) (cs := C.cpTReps.c0) rfl rfl (by quickRfl)
    (by quickRfl)
  have e1 := bind_txt (P := RPT.E (lget RPT.OFF 1)) (cs := C.cpTReps.c1) rfl rfl (by quickRfl)
    (by quickRfl)
  have er : cpTReps = [CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.cpTReps.c0),
      CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.cpTReps.c1)] := by
    rw [← C.cpTReps.e0, ← C.cpTReps.e1]
    rfl
  have hN : RPT.N = 140 := rfl
  refine classCheck_ofE (k := 2) (GP := RPT.GP) (GIP := RPT.GIP) (CI := RPT.CI) (E := RPT.E)
    (P := RPT.P) (L := RPT.L) (K := RPT.K) (Ss := RPT.S) (SI := RPT.SI) (CS := RPT.CS)
    (OFF := RPT.OFF) (N := RPT.N)
    c2A_binds c2A_perm C2A.hl (by norm_num) (fun l hl => ?_) (fun l hl => ?_) (fun l hl => ?_)
    (by rw [er, e0, e1]; rfl) (by quickRfl) (by quickRfl) (Nat.eq_of_beq_eq_true cpT_cnt)
    (fun j hj => CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RPTB.all j
      (by rw [hN] at hj; exact hj)) rfl (fun i hi => ?_)
  · interval_cases l <;> exact ⟨Nat.eq_of_beq_eq_true (by quickRfl),
      Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · interval_cases l <;> exact ⟨by quickRfl, by quickRfl⟩
  · interval_cases l <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  · change i < 2 at hi
    interval_cases i <;>
      exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem crUE : crUCheck = true := by
  unfold crUCheck
  rw [Bool.and_eq_true]
  refine ⟨chainCheck_of crU_binds (by norm_num) crU_chain hou hou (fun j hj => ?_) (by quickRfl)
    (by quickRfl) (fun j hj => ?_) (fun j hj => ?_) (by quickRfl) (by quickRfl) (fun j hj => ?_), ?_⟩
  · interval_cases j <;> quickRfl
  · interval_cases j <;> quickRfl
  · interval_cases j <;> quickRfl
  · interval_cases j <;> quickRfl
  have e0 := bind_txt (P := RU.E (lget RU.OFF 0)) (cs := C.crUReps.c0) rfl rfl (by quickRfl)
    (by quickRfl)
  have e1 := bind_txt (P := RU.E (lget RU.OFF 1)) (cs := C.crUReps.c1) rfl rfl (by quickRfl)
    (by quickRfl)
  have er : crUReps = [CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.crUReps.c0),
      CFSG.Sporadic.Fi23.Native.natsOf (String.ofList C.crUReps.c1)] := by
    rw [← C.crUReps.e0, ← C.crUReps.e1]
    rfl
  have hN : RU.N = 84 := rfl
  refine classCheck_ofE (k := 3) (GP := RU.GP) (GIP := RU.GIP) (CI := RU.CI) (E := RU.E)
    (P := RU.P) (L := RU.L) (K := RU.K) (Ss := RU.S) (SI := RU.SI) (CS := RU.CS) (OFF := RU.OFF)
    (N := RU.N) crU_binds crU_perm CRU.hl (by norm_num) (fun l hl => ?_) (fun l hl => ?_)
    (fun l hl => ?_) (by rw [er, e0, e1]; rfl) (by quickRfl) (by quickRfl)
    (Nat.eq_of_beq_eq_true crU_cnt)
    (fun j hj => CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RUB.all j
      (by rw [hN] at hj; exact hj)) rfl (fun i hi => ?_)
  · interval_cases l <;> exact ⟨Nat.eq_of_beq_eq_true (by quickRfl),
      Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · interval_cases l <;> exact ⟨by quickRfl, by quickRfl⟩
  · interval_cases l <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  · change i < 2 at hi
    interval_cases i <;>
      exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem crTE : crTCheck = true := by
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
  refine classCheck_ofE (k := 3) (GP := RT.GP) (GIP := RT.GIP) (CI := RT.CI) (E := RT.E)
    (P := RT.P) (L := RT.L) (K := RT.K) (Ss := RT.S) (SI := RT.SI) (CS := RT.CS) (OFF := RT.OFF)
    (N := RT.N) crT_binds crT_perm CRT.hl (by norm_num) (fun l hl => ?_) (fun l hl => ?_)
    (fun l hl => ?_) (by rw [er, e0, e1, e2, e3]; rfl) (by quickRfl) (by quickRfl)
    (Nat.eq_of_beq_eq_true crT_cnt)
    (fun j hj => CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RTB.all j
      (by rw [hN] at hj; exact hj)) rfl (fun i hi => ?_)
  · interval_cases l <;> exact ⟨Nat.eq_of_beq_eq_true (by quickRfl),
      Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · interval_cases l <;> exact ⟨by quickRfl, by quickRfl⟩
  · interval_cases l <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  · change i < 4 at hi
    interval_cases i <;>
      exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem facts10021E : cpACheck = true ∧ crACheck = true ∧ cpTCheck = true ∧ crTCheck = true ∧
    crUCheck = true :=
  ⟨cpAE, crAE, cpTE, crTE, crUE⟩

end CertificateChecks.KernelJ2Cover

end
