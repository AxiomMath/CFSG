module

public import Certificates.Kernel.HeOrb.Checks
public import CFSG.Certificates.Kernel.Spor.HeVOrb
import CFSG.Certificates.Kernel.Spor.VOrbSound
public import CFSG.Certificates.Kernel.SporSch.LyMatSound

public section

namespace CFSG.KD.HeOrb

open CFSG.KC.HeOrb CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.PEnum CFSG.KS.Row CFSG.KS.VO
  CFSG.KS.HeVO CFSG.KS.SporSch.LyM CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native

@[expose] noncomputable def T (i : Nat) : Array Nat := keyOf 50 12 (code PT i)

@[expose] noncomputable def OJ : VOrbit := vRec 8330 T AL BE PA LA

theorem cRM_eq : cRM = 2 ^ 600 - 1 := by
  unfold cRM
  change (1 <<< 600) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem fld600 (Y o : Nat) : Nat.land (Nat.shiftRight Y o) cRM = Y / 2 ^ o % 2 ^ 600 := by
  rw [cRM_eq, land_eq, Nat.and_two_pow_sub_one_eq_mod]
  change Y >>> o % 2 ^ 600 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem code_eq (i : Nat) : code PT i = PT (i / 32) / 2 ^ (600 * (i % 32)) % 2 ^ 600 := by
  unfold code rg
  rw [fld600]
  have e1 : Nat.add 0 (Nat.shiftRight i 5) = i / 32 := by
    change 0 + i >>> 5 = _
    rw [Nat.zero_add, Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land i 31 = i % 32 := by
    rw [land_eq]
    exact Nat.and_two_pow_sub_one_eq_mod i 5
  rw [e1, e2]
  rfl

theorem code_lt (i : Nat) : code PT i < 2 ^ (12 * 50) := by
  rw [code_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem mat_parts : constsOK 7 12 600 50 8 cL cH cCM cRM cONE cLV cHV = true ∧ vldH TA = true ∧
    vldH TB = true ∧ trK (payRunP 7 50 12 600 SA.chars 0 0 0) TA = true ∧
    trK (payRunP 7 50 12 600 SB.chars 0 0 0) TB = true :=
  matK_spec mat_ok

theorem matA_eq : matA () = unpackL 50 12 600 (payRunP 7 50 12 600 SA.chars 0 0 0) := by
  have e : matA () = rowsOf 7 50 seedA := rfl
  rw [e, SA.eq, payRunP_eq (w := 12) (S := 600) _ (by norm_num) (by norm_num) (by norm_num)]

theorem matB_eq : matB () = unpackL 50 12 600 (payRunP 7 50 12 600 SB.chars 0 0 0) := by
  have e : matB () = rowsOf 7 50 seedB := rfl
  rw [e, SB.eq, payRunP_eq (w := 12) (S := 600) _ (by norm_num) (by norm_num) (by norm_num)]

theorem trA : ∀ i < 50, ∀ j < 50, ((unpackL 50 12 600 TA)[i]!)[j]! = ((matA ())[j]!)[i]! := by
  rw [matA_eq]
  exact trK_sound mat_parts.2.2.2.1

theorem trB : ∀ i < 50, ∀ j < 50, ((unpackL 50 12 600 TB)[i]!)[j]! = ((matB ())[j]!)[i]! := by
  rw [matB_eq]
  exact trK_sound mat_parts.2.2.2.2

theorem vld_eq {X : Nat} (h : vldH X = true) : validM 7 (50 * 600) cL cH X = true := h

theorem T_row {i : Nat} : T i = (unpackL 50 12 600 (PT (i / 32)))[i % 32]! := by
  unfold T
  rw [code_eq, unpackL_row (by norm_num) (by have := Nat.mod_lt i (show 0 < 32 by norm_num); omega)]

theorem img {X TX : Nat} {M : Array (Array Nat)} (hX : vldH X = true) (hT : vldH TX = true)
    (htr : ∀ i < 50, ∀ j < 50, ((unpackL 50 12 600 TX)[i]!)[j]! = (M[j]!)[i]!) {r : Nat}
    (hr : r < 50) :
    mulVec 7 50 M (unpackL 50 12 600 X)[r]! = keyOf 50 12 (rowF (mulH X TX) r) := by
  rw [← mulM_tr htr hr, (mulR_eq mat_parts.1 (vld_eq hX) (vld_eq hT)).1,
    unpackL_row (by norm_num) hr]
  unfold rowF
  rw [fld600]
  rfl

theorem chunk {len : Nat} (hl : 0 < len) (i : Nat) :
    Nat.add (Nat.mul len (i / len)) (i % len) = i ∧ i % len < len := by
  refine ⟨?_, Nat.mod_lt _ hl⟩
  change len * (i / len) + i % len = i
  exact Nat.div_add_mod i len

theorem blk {s : Nat} (hs : s < 261) : blkK PT AL BE TA TB s = true := by
  have hc : s / 9 < 29 := by omega
  have h := B.all (s / 9) hc
  unfold famB at h
  have := allN_spec h (s % 9) (chunk (by norm_num) s).2
  rwa [(chunk (by norm_num) s).1] at this

theorem pt_facts {i : Nat} (hi : i < 8330) : r32 AL i < 8330 ∧ r32 BE i < 8330 ∧
    mulVec 7 50 (matA ()) (T i) = T (r32 AL i) ∧ mulVec 7 50 (matB ()) (T i) = T (r32 BE i) := by
  have h := blkK_spec (blk (s := i / 32) (by omega))
  obtain ⟨ha, hb, hA, hB⟩ := h.2 i rfl hi
  have hr : i % 32 < 50 := by have := Nat.mod_lt i (show 0 < 32 by norm_num); omega
  refine ⟨ha, hb, ?_, ?_⟩
  · rw [T_row, img h.1 mat_parts.2.1 trA hr, hA]
    rfl
  · rw [T_row, img h.1 mat_parts.2.2.1 trB hr, hB]
    rfl

theorem hd_parts : r32 PA 0 = 0 ∧ r32 LA 0 = 0 ∧
    Nat.beq (vorbCnt (nat_lit 8330) AL BE PA LA) (nat_lit 8330) = true ∧
    ∀ j < 50, code PT 0 / 2 ^ (12 * j) % 2 ^ 12 = R.getD j 0 :=
  hdK_spec hd_ok

theorem rootVec_eq : rootVec () = Array.ofFn (n := 50) fun j => R.getD j.val 0 := by
  unfold rootVec
  rw [RD.eq, String.toList_ofList]
  decide +kernel

theorem T_zero : T 0 = rootVec () := by
  rw [rootVec_eq]
  unfold T keyOf
  exact congrArg Array.ofFn (funext fun j => hd_parts.2.2.2 j.val j.isLt)

theorem T_inj : ∀ i < 8330, ∀ j < 8330, T i = T j → i = j := by
  intro i hi j hj e
  exact codes_inj_of_sort (srtK_spec srt_ok) i hi j hj (keyOf_inj (by norm_num) (code_lt i)
    (code_lt j) e)

theorem orbitData_eq : orbitData () = OJ := by
  have hc : vorbCnt (nat_lit 8330) AL BE PA LA = nat_lit 8330 :=
    Nat.eq_of_beq_eq_true hd_parts.2.2.1
  unfold orbitData
  rw [← T_zero]
  exact vecBFS_of (N := nat_lit 8330) (cap := 8330) (T := T) (AL := AL) (BE := BE) (PA := PA)
    (LA := LA) (by norm_num) (by norm_num) T_inj (fun i hi => pt_facts hi) hc hd_parts.1
    hd_parts.2.1

theorem alpha_ap {x : Nat} (hx : x < 8330) : ap OJ.alpha x = r32 AL x := vRec_alpha hx

theorem beta_ap {x : Nat} (hx : x < 8330) : ap OJ.beta x = r32 BE x := vRec_beta hx

end CFSG.KD.HeOrb

end
