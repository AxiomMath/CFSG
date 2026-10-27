module

public import Certificates.Kernel.He2111.Checks
public import CFSG.Sporadic.HeldB.CertPBridgeCheckInputs
import Certificates.Kernel.HeOrb.Final
import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.MonsterB.Co2PermSound

public section

namespace CFSG.KD.He2111

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KC.He2111 CFSG.KD.HeOrb CFSG.Sporadic.HeldB
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem unpack_get {n w P i : Nat} (hi : i < n) :
    (CFSG.KS.Raw.unpack n w P)[i]! = pg w (mask w) P i := by
  rw [CFSG.KS.Raw.unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem mask14 : mask 14 = 16383 := rfl

theorem br_get {x : Nat} (hx : x < 8330) : heBridgeArr[x]! = e14 (BrT.F 0) x := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound BrT.all 0 (by decide)
  rw [← BrT.eq, Nat.mul_zero] at h
  unfold heBridgeArr
  rw [h, unpack_get hx, mask14]
  rfl

theorem gen_get {k x : Nat} (hk : k < 2) (hx : x < 8330) : (heGen k)[x]! = e14 (GnT.F k) x := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound GnT.all k hk
  rw [← GnT.eq] at h
  unfold heGen
  rw [h, unpack_get hx, mask14]
  rfl

theorem brK_spec {x : Nat} (hx : x < 8330) :
    e14 (BrT.F 0) x < 8330 ∧ e14 (GnT.F 0) x < 8330 ∧ e14 (GnT.F 1) x < 8330 ∧
      r32 PI (e14 (BrT.F 0) x) = x ∧
      r32 AL (e14 (BrT.F 0) x) = e14 (BrT.F 0) (e14 (GnT.F 0) x) ∧
      r32 BE (e14 (BrT.F 0) x) = e14 (BrT.F 0) (e14 (GnT.F 1) x) := by
  have hb : x / 1000 < 9 := by omega
  have h := Br.all (x / 1000) hb
  unfold famBr brSl at h
  have h2 := allN_spec h (x % 1000) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h2
  have ei : Nat.add (Nat.mul 1000 (x / 1000)) (x % 1000) = x := Nat.div_add_mod x 1000
  have hx' : Nat.blt x (nat_lit 8330) = true := by rw [Nat.blt_eq]; exact hx
  rw [ei] at h2
  have h3 := CFSG.KS.HeVO.bIf_of h2 hx'
  unfold brK at h3
  rw [strictB_eq, strictB_eq, strictB_eq] at h3
  generalize e14 (BrT.F 0) x = y at h3 ⊢
  obtain ⟨h1, h3⟩ := (bAnd_iff _ _).1 h3
  obtain ⟨hu, h3⟩ := (bAnd_iff _ _).1 h3
  obtain ⟨hv, h3⟩ := (bAnd_iff _ _).1 h3
  obtain ⟨hp, h3⟩ := (bAnd_iff _ _).1 h3
  obtain ⟨ha, hb⟩ := (bAnd_iff _ _).1 h3
  rw [Nat.blt_eq] at h1 hu hv
  exact ⟨h1, hu, hv, Nat.eq_of_beq_eq_true hp, Nat.eq_of_beq_eq_true ha, Nat.eq_of_beq_eq_true hb⟩

theorem allLt_iff {n : Nat} {p : Nat → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  exact ⟨fun h i hi => h ⟨i, hi⟩ (List.mem_finRange _), fun h i _ => h i.val i.isLt⟩

theorem heBridge_ok : heBridgeOK = true := by
  unfold heBridgeOK
  rw [orbitData_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine CFSG.KC.Co2Mem.isInvA_invCand (fun i hi => ?_) (fun i j hi hj e => ?_)
    · rw [br_get hi]
      exact (brK_spec hi).1
    · rw [br_get hi, br_get hj] at e
      rw [← (brK_spec hi).2.2.2.1, ← (brK_spec hj).2.2.2.1, e]
  · rw [allLt_iff]
    intro i hi
    obtain ⟨h1, h2, -, -, h5, -⟩ := brK_spec hi
    rw [br_get hi, gen_get (by norm_num) hi, br_get h2, alpha_ap h1, h5]
    exact beq_self_eq_true _
  · rw [allLt_iff]
    intro i hi
    obtain ⟨h1, -, h3, -, -, h6⟩ := brK_spec hi
    rw [br_get hi, gen_get (by norm_num) hi, br_get h3, beta_ap h1, h6]
    exact beq_self_eq_true _

end CFSG.KD.He2111

end
