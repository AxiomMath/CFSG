
module

public import Certificates.Kernel.J2Cover.AutChains
public import Certificates.Kernel.J2Cover.Orb
public import Certificates.Kernel.J2Cover.K20A
public import Certificates.Kernel.J2Cover.ModelsBind
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.J2CoverSound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover

theorem hb' : autStrong[1]! = unpack 315 9 (PA.S 1) := binds.2.2.2.2.1 1 (by omega)

theorem orbC : allLt 315 (fun i => ap (CFSG.Sporadic.J2.Native.orbitData ()).alpha i ==
    (autStrong[0]!)[i]! && ap (CFSG.Sporadic.J2.Native.orbitData ()).beta i ==
      (autStrong[1]!)[i]!) = true := by
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_
  have ha' := Nat.le_of_ble_eq_true (allN_spec kLtA i hi)
  have hb'' := Nat.le_of_ble_eq_true (allN_spec kLtB i hi)
  rw [alpha_eq, beta_eq, ha, hb']
  unfold ap
  rw [getElem!_ofFn' hi, getElem!_ofFn' hi, getElem!_unpack hi, getElem!_unpack hi,
    UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le ha' (by decide)),
    UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hb'' (by decide)),
    Nat.eq_of_beq_eq_true (allN_spec kA i hi), Nat.eq_of_beq_eq_true (allN_spec kB i hi)]
  simp

theorem cOU : CnN 315 9 OU := by quickRfl

theorem cTA : CnN 315 9 TA := by quickRfl

theorem cPA (j : Nat) (hj : j < 7) : CnN 315 9 (PA.S j) := by
  interval_cases j <;> quickRfl

theorem outerC : inP outerArr = false ∧
    inP (compA 315 outerArr (compA 315 autStrong[0]! outerArr)) = true ∧
    inP (compA 315 outerArr (compA 315 autStrong[1]! outerArr)) = true := by
  have c0 := cPA 0 (by omega)
  have c1 := cPA 1 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have h : (!inP outerArr) = true := by
      unfold inP autLevels
      rw [hou, CFSG.KC.J2Cover.siftK_eq binds perm PA.hl cOU]
      quickRfl
    revert h
    cases inP outerArr <;> simp
  · rw [hou, ha, compA_unpackN c0 cOU, compA_unpackN cOU (canon_pcN c0 cOU)]
    exact inP_of rfl (by quickRfl) (by quickRfl) (by quickRfl)
  · rw [hou, hb', compA_unpackN c1 cOU, compA_unpackN cOU (canon_pcN c1 cOU)]
    exact inP_of rfl (by quickRfl) (by quickRfl) (by quickRfl)

theorem twoA_in : inP twoAArr = true := inP_of hta (by quickRfl) (by quickRfl) (by quickRfl)

theorem centGens {S : Array (Array Nat)} {base : Array Nat} {kS nb BP : Nat} {PS : Nat → Nat} {x : Array Nat}
    {X : Nat} (hb : Binds 315 9 PS kS nb BP S base) (h2 : 2 ≤ kS) (hx : x = unpack 315 9 X)
    (cx : CnN 315 9 X) (c : ∀ j < 2, CnN 315 9 (PS j))
    (hz : ∀ j < 2, Nat.beq (Nat.shiftRight (PS j) (315 * 9)) 0 = true)
    (hs : ∀ j < 2, siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 (PS j) = true)
    (hc : ∀ j < 2, Nat.beq (pcomp 315 9 (mask 9) (PS j) X) (pcomp 315 9 (mask 9) X (PS j)) = true) :
    inP S[0]! = true ∧ inP S[1]! = true ∧ commA S[0]! x = true ∧ commA S[1]! x = true :=
  ⟨inP_of (hb.2.2.2.2.1 0 (by omega)) (hz 0 (by omega)) (range_of_canonK (c 0 (by omega)))
      (hs 0 (by omega)),
    inP_of (hb.2.2.2.2.1 1 (by omega)) (hz 1 (by omega)) (range_of_canonK (c 1 (by omega)))
      (hs 1 (by omega)),
    commA_of (hb.2.2.2.2.1 0 (by omega)) hx (c 0 (by omega)) cx (hc 0 (by omega)),
    commA_of (hb.2.2.2.2.1 1 (by omega)) hx (c 1 (by omega)) cx (hc 1 (by omega))⟩

theorem c2B_gens : inP cent2BStrong[0]! = true ∧ inP cent2BStrong[1]! = true ∧
    commA cent2BStrong[0]! autStrong[0]! = true ∧ commA cent2BStrong[1]! autStrong[0]! = true :=
  centGens c2B_binds (by norm_num) ha (cPA 0 (by omega))
    (fun j hj => by interval_cases j <;> quickRfl) (fun j hj => by interval_cases j <;> quickRfl)
    (fun j hj => by interval_cases j <;> quickRfl) (fun j hj => by interval_cases j <;> quickRfl)

theorem c2A_gens : inP cent2AStrong[0]! = true ∧ inP cent2AStrong[1]! = true ∧
    commA cent2AStrong[0]! twoAArr = true ∧ commA cent2AStrong[1]! twoAArr = true :=
  centGens c2A_binds (by norm_num) hta cTA
    (fun j hj => by interval_cases j <;> quickRfl) (fun j hj => by interval_cases j <;> quickRfl)
    (fun j hj => by interval_cases j <;> quickRfl) (fun j hj => by interval_cases j <;> quickRfl)

theorem cOu_gens : inP centOuterStrong[0]! = true ∧ inP centOuterStrong[1]! = true ∧
    commA centOuterStrong[0]! outerArr = true ∧ commA centOuterStrong[1]! outerArr = true :=
  centGens cOu_binds (by norm_num) hou cOU
    (fun j hj => by interval_cases j <;> quickRfl) (fun j hj => by interval_cases j <;> quickRfl)
    (fun j hj => by interval_cases j <;> quickRfl) (fun j hj => by interval_cases j <;> quickRfl)

theorem sylowC : rawChainOK 315 (sylowStrong.extract 0 3) sylowStrong sylowBase sylowWords 4 = true ∧
    rawOrbitSizes 315 sylowStrong sylowBase = [64, 4] ∧
    inP (compA 315 sylowStrong[0]! outerArr) = true ∧
    inP (compA 315 sylowStrong[1]! outerArr) = true ∧
    inP (compA 315 sylowStrong[2]! outerArr) = true := by
  have hs : ∀ j < 3, inP (compA 315 sylowStrong[j]! outerArr) = true := by
    intro j hj
    have cj : CnN 315 9 (SYL.S j) := by interval_cases j <;> quickRfl
    rw [syl_binds.2.2.2.2.1 j (by omega), hou, compA_unpackN cj cOU]
    exact inP_of rfl (by interval_cases j <;> quickRfl) (by interval_cases j <;> quickRfl)
      (by interval_cases j <;> quickRfl)
  exact ⟨syl_chain.1, syl_chain.2, hs 0 (by omega), hs 1 (by omega), hs 2 (by omega)⟩

end CertificateChecks.KernelJ2Cover

end
