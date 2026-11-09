module

public import Certificates.Kernel.NT44.Pack
public import Certificates.Kernel.NT44.Pack2
public import Certificates.Data.Kernel.Misc.ConjTab
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.SchreierChainData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.KC.Misc.ConjTab
open CFSG.KC.Enum (permOK pidn pcomp strictB)
open CFSG.KS (mask)
open CFSG.KS.Prim (wordEqK commK compEqK)
open CFSG.KS.Raw (wordK)
open CFSG.KC.LQT.P (allN)

theorem nt44_fwd : allN 2 (fun i => wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2
    (fwd ())[i]! (nt44V i)) = true := by quickRfl

theorem nt44_inv_v : allN 2 (fun i => permOK 2688 12 (mask 12) (2688 * 12) (nt44V i)
    (nt44VI i)) = true := by quickRfl

@[expose] noncomputable def nt44CoverOn (ws : List (List (Fin 2 × Bool))) : Bool :=
  (ws.map (List.map CFSG.Certificates.schreierLetterCode)).all (fun r =>
    wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI 2 r (pidn 2688 12))

@[expose] noncomputable def nt44RelOK (r : List Int) : Bool :=
  strictB (wordK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI r) fun R =>
    wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI 2 r R &&
      commK 2688 12 (mask 12) (2688 * 12) (nt44V 0) R &&
      commK 2688 12 (mask 12) (2688 * 12) (nt44V 1) R

@[expose] noncomputable def nt44Pow4OK (z : List Int) : Bool :=
  strictB (wordK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI z) fun Z =>
    strictB (pcomp 2688 12 (mask 12) Z Z) fun Z2 =>
      wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI 2 z Z &&
        compEqK 2688 12 (mask 12) (2688 * 12) Z Z Z2 &&
        compEqK 2688 12 (mask 12) (2688 * 12) Z2 Z2 (pidn 2688 12)

@[expose] def nt44CWT : List (List (Fin 2 × Bool)) :=
  (List.finRange 2).map fun i =>
    (i, false) :: CFSG.LieType.Multipliers.commWords (CFSG.LieType.Multipliers.L34.coverPairs i)

theorem nt44_rels : (CFSG.LieType.Multipliers.L34.rels.map
    (List.map CFSG.Certificates.schreierLetterCode)).all nt44RelOK = true := by quickRfl

theorem nt44_coverT : nt44CoverOn nt44CWT = true := by quickRfl

theorem nt44_coverE : nt44CoverOn [CFSG.LieType.Multipliers.L34.bFive,
    CFSG.LieType.Multipliers.L34.wpow CFSG.LieType.Multipliers.L34.zThree 3] = true := by
  quickRfl

theorem nt44_zOne4 :
    nt44Pow4OK (CFSG.LieType.Multipliers.L34.zOne.map CFSG.Certificates.schreierLetterCode) =
      true := by quickRfl

theorem nt44_zTwo4 :
    nt44Pow4OK (CFSG.LieType.Multipliers.L34.zTwo.map CFSG.Certificates.schreierLetterCode) =
      true := by quickRfl

theorem nt44_z : wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI 2
    (CFSG.LieType.Multipliers.L34.zThree.map CFSG.Certificates.schreierLetterCode)
    (pidn 2688 12) = true := by
  quickRfl

theorem nt44_rev : allN 2 (fun i => wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI 2
    (rev ())[i]! (nt44KS i)) = true := by quickRfl

noncomputable def nt44PwAt (i : Nat) : Bool :=
  wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2 (pw ())[i]! (nt44P0 i)

theorem nt44_pw0 : nt44PwAt 0 = true := by quickRfl
theorem nt44_pw1 : nt44PwAt 1 = true := by quickRfl
theorem nt44_pw2 : nt44PwAt 2 = true := by quickRfl
theorem nt44_pw3 : nt44PwAt 3 = true := by quickRfl
theorem nt44_pw4 : nt44PwAt 4 = true := by quickRfl
theorem nt44_pw5 : nt44PwAt 5 = true := by quickRfl
theorem nt44_pw6 : nt44PwAt 6 = true := by quickRfl
theorem nt44_pw7 : nt44PwAt 7 = true := by quickRfl
theorem nt44_pw8 : nt44PwAt 8 = true := by quickRfl

theorem nt44_pwAt : ∀ i < 9, nt44PwAt i = true
  | 0, _ => nt44_pw0
  | 1, _ => nt44_pw1
  | 2, _ => nt44_pw2
  | 3, _ => nt44_pw3
  | 4, _ => nt44_pw4
  | 5, _ => nt44_pw5
  | 6, _ => nt44_pw6
  | 7, _ => nt44_pw7
  | 8, _ => nt44_pw8
  | i + 9, hi => absurd hi (by omega)

noncomputable def nt44NormAt (k : Nat) : Bool :=
  allN 2 fun j => wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2 (nw ())[k]!.left[j]!
    (cj3 2688 12 (nt44L (k + 1)) (nt44KS j) (nt44LI (k + 1)))

theorem nt44_norm0 : nt44NormAt 0 = true := by quickRfl
theorem nt44_norm1 : nt44NormAt 1 = true := by quickRfl
theorem nt44_norm2 : nt44NormAt 2 = true := by quickRfl
theorem nt44_norm3 : nt44NormAt 3 = true := by quickRfl

theorem nt44_normAt : ∀ k < 4, nt44NormAt k = true
  | 0, _ => nt44_norm0
  | 1, _ => nt44_norm1
  | 2, _ => nt44_norm2
  | 3, _ => nt44_norm3
  | k + 4, hk => absurd hk (by omega)

theorem nt44_allN_lt {F : Nat → Bool} : ∀ m, (∀ k < m, F k = true) → allN m F = true
  | 0, _ => rfl
  | m + 1, h => by
    change CFSG.KC.Ord.andB (F m) (allN m F) = true
    rw [h m (by omega), nt44_allN_lt m fun k hk => h k (by omega)]
    rfl

theorem nt44_norm : allN 4 (fun k => allN 2 fun j =>
    wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2 (nw ())[k]!.left[j]!
      (cj3 2688 12 (nt44L (k + 1)) (nt44KS j) (nt44LI (k + 1)))) = true :=
  nt44_allN_lt 4 nt44_normAt

theorem nt44_pw : allN 9 (fun i => wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2
    (pw ())[i]! (nt44P0 i)) = true :=
  nt44_allN_lt 9 nt44_pwAt

end CertificateChecks.KernelNT44

end
