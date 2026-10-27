
module

public import Certificates.Kernel.J2Cover.ClassOf
public import Certificates.Kernel.J2Cover.KerChains
public import Certificates.Kernel.J2Cover.AutChains
public import Certificates.Kernel.J2Cover.KerReps
public import Certificates.Kernel.LocalComp.Child3Lemmas
public import Certificates.Kernel.LocalComp.BlockGen
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelJ2Cover.OU 9 CFSG.ComponentClassification.J2Cover.outerArr

#ks_perm CertificateChecks.KernelJ2Cover.TA 9 CFSG.ComponentClassification.J2Cover.twoAArr

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText TxtKernel
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.Kernel

theorem chainCheck_of {S : Array (Array Nat)} {base : Array Nat} {W : Array (List Int)}
    {sizes : List Nat} {x : Array Nat} {kS nb BP : Nat} {PS : Nat → Nat} {X OU : Nat}
    (hb : Binds 315 9 PS kS nb BP S base) (h3 : 3 ≤ kS)
    (hc : rawChainOK 315 (S.extract 0 3) S base W 4 = true ∧ rawOrbitSizes 315 S base = sizes)
    (hx : x = unpack 315 9 X) (hou : outerArr = unpack 315 9 OU)
    (hcan : ∀ j < 3, canonK 315 9 (mask 9) (315 * 9) (PS j) = true)
    (hcx : canonK 315 9 (mask 9) (315 * 9) X = true)
    (hco : canonK 315 9 (mask 9) (315 * 9) OU = true)
    (hz : ∀ j < 2, Nat.beq (Nat.shiftRight (PS j) (315 * 9)) 0 = true)
    (hs : ∀ j < 2, siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 (PS j) = true)
    (hz2 : Nat.beq (Nat.shiftRight (pcomp 315 9 (mask 9) (PS 2) OU) (315 * 9)) 0 = true)
    (hs2 : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0
      (pcomp 315 9 (mask 9) (PS 2) OU) = true)
    (hcm : ∀ j < 3, Nat.beq (pcomp 315 9 (mask 9) (PS j) X) (pcomp 315 9 (mask 9) X (PS j)) =
      true) :
    CFSG.ComponentClassification.J2Cover.Kernel.chainCheck S base W sizes x = true := by
  have hS : ∀ j < 3, S[j]! = unpack 315 9 (PS j) := fun j hj => hb.2.2.2.2.1 j (by omega)
  have hcomm : ∀ j < 3, commA S[j]! x = true := by
    intro j hj
    unfold commA
    rw [hS j hj, hx, compA_unpackN (hcan j hj) hcx, compA_unpackN hcx (hcan j hj),
      eqA_unpackN (canon_pcN (hcan j hj) hcx) (canon_pcN hcx (hcan j hj))]
    exact hcm j hj
  unfold CFSG.ComponentClassification.J2Cover.Kernel.chainCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨hc.1, hc.2⟩, ?_⟩, ?_⟩, ?_⟩, hcomm 0 (by omega)⟩, hcomm 1 (by omega)⟩,
    hcomm 2 (by omega)⟩
  · exact inP_of (hS 0 (by omega)) (hz 0 (by omega)) (range_of_canonK (hcan 0 (by omega)))
      (hs 0 (by omega))
  · exact inP_of (hS 1 (by omega)) (hz 1 (by omega)) (range_of_canonK (hcan 1 (by omega)))
      (hs 1 (by omega))
  · rw [hS 2 (by omega), hou, compA_unpackN (hcan 2 (by omega)) hco]
    exact inP_of rfl hz2 (range_of_canonK (canon_pcN (hcan 2 (by omega)) hco)) hs2

theorem hou : outerArr = unpack 315 9 OU := arrBind_sound (by quickRfl)

theorem hta : twoAArr = unpack 315 9 TA := arrBind_sound (by quickRfl)

theorem ha : autStrong[0]! = unpack 315 9 (PA.S 0) := binds.2.2.2.2.1 0 (by omega)

theorem cpA_cnt : Nat.beq (prodCnt 315 9 2 C2B.LR C2B.TR (ord4K 315 9)) 0 = true := by quickRfl

theorem crA_cnt : Nat.beq (prodCnt 315 9 2 CRA.LR CRA.TR (ord4K 315 9)) RA.N = true := by quickRfl

theorem cpT_cnt : Nat.beq (prodCnt 315 9 3 C2A.LR C2A.TR (ord4K 315 9)) RPT.N = true := by quickRfl

theorem crU_cnt : Nat.beq (prodCnt 315 9 2 CRU.LR CRU.TR (ord4K 315 9)) RU.N = true := by quickRfl

theorem cpA : cpACheck = true := by
  unfold cpACheck
  refine classCheck_of (k := 2) (GP := C2B.S) (GIP := C2B.SI) (CI := fun _ => 0)
    (E := fun _ => 0) (P := fun _ => 0) (L := fun _ => 0) (K := fun _ => 0) (Ss := fun _ => 0)
    (SI := fun _ => 0) (CS := []) (OFF := []) (N := 0) c2B_binds c2B_perm C2B.hl (by norm_num)
    (fun _ _ => ⟨rfl, rfl⟩) (fun l hl => ?_) (fun l hl => ?_) rfl (by quickRfl) rfl
    (Nat.eq_of_beq_eq_true cpA_cnt) (fun j hj => absurd hj (Nat.not_lt_zero j)) rfl
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  · interval_cases l <;> exact ⟨by quickRfl, by quickRfl⟩
  · interval_cases l <;> exact Nat.eq_of_beq_eq_true (by quickRfl)

@[expose] noncomputable def fRA (j : Nat) : Bool :=
  repK 315 9 RA.GP RA.GIP 3 RA.CS RA.OFF RA.CI RA.E RA.P RA.L RA.K RA.S RA.SI RA.N 4000 j

#lc_blocks RAB fRA 140 8

theorem crA : crACheck = true := by
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
  refine classCheck_of (k := 3) (GP := RA.GP) (GIP := RA.GIP) (CI := RA.CI) (E := RA.E) (P := RA.P)
    (L := RA.L) (K := RA.K) (Ss := RA.S) (SI := RA.SI) (CS := RA.CS) (OFF := RA.OFF) (N := RA.N)
    crA_binds crA_perm CRA.hl (by norm_num) (fun l hl => ?_) (fun l hl => ?_) (fun l hl => ?_)
    (by rw [er, e0, e1, e2]; rfl) (by quickRfl) (by quickRfl) (Nat.eq_of_beq_eq_true crA_cnt)
    (fun j hj => CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RAB.all j
      (by rw [hN] at hj; exact hj)) rfl (fun i hi => ?_)
  · interval_cases l <;> exact ⟨Nat.eq_of_beq_eq_true (by quickRfl),
      Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · interval_cases l <;> exact ⟨by quickRfl, by quickRfl⟩
  · interval_cases l <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  · change i < 3 at hi
    interval_cases i <;>
      exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

@[expose] noncomputable def fRPT (j : Nat) : Bool :=
  repK 315 9 RPT.GP RPT.GIP 2 RPT.CS RPT.OFF RPT.CI RPT.E RPT.P RPT.L RPT.K RPT.S RPT.SI RPT.N 4000 j

#lc_blocks RPTB fRPT 140 8

theorem cpT : cpTCheck = true := by
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
  refine classCheck_of (k := 2) (GP := RPT.GP) (GIP := RPT.GIP) (CI := RPT.CI) (E := RPT.E)
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

@[expose] noncomputable def fRU (j : Nat) : Bool :=
  repK 315 9 RU.GP RU.GIP 3 RU.CS RU.OFF RU.CI RU.E RU.P RU.L RU.K RU.S RU.SI RU.N 4000 j

#lc_blocks RUB fRU 84 8

theorem crU : crUCheck = true := by
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
  refine classCheck_of (k := 3) (GP := RU.GP) (GIP := RU.GIP) (CI := RU.CI) (E := RU.E) (P := RU.P)
    (L := RU.L) (K := RU.K) (Ss := RU.S) (SI := RU.SI) (CS := RU.CS) (OFF := RU.OFF) (N := RU.N)
    crU_binds crU_perm CRU.hl (by norm_num) (fun l hl => ?_) (fun l hl => ?_) (fun l hl => ?_)
    (by rw [er, e0, e1]; rfl) (by quickRfl) (by quickRfl) (Nat.eq_of_beq_eq_true crU_cnt)
    (fun j hj => CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RUB.all j
      (by rw [hN] at hj; exact hj)) rfl (fun i hi => ?_)
  · interval_cases l <;> exact ⟨Nat.eq_of_beq_eq_true (by quickRfl),
      Nat.eq_of_beq_eq_true (by quickRfl)⟩
  · interval_cases l <;> exact ⟨by quickRfl, by quickRfl⟩
  · interval_cases l <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  · change i < 2 at hi
    interval_cases i <;>
      exact ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelJ2Cover

end
