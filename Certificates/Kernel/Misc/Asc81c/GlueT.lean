module

import Certificates.Kernel.Misc.Asc81c.ChecksT
import Certificates.Kernel.Misc.Asc81c.ChecksT4A
import Certificates.Kernel.Misc.Asc81c.ChecksT4B
import Certificates.Kernel.Misc.Asc81c.ChecksT4C
import Certificates.Kernel.Misc.Asc81c.ChecksT4D
import Certificates.Kernel.Misc.Asc81c.Glue
public import Certificates.Kernel.Misc.Asc81c.LinSound
import CFSG.Monster.B.Co2.PermArr
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check CFSG.Monster.B.Co2.Native CFSG.KGroups.Native

theorem mem_allLists {N : Nat} : ∀ {k : Nat} {c : List Nat}, c ∈ allLists N k →
    c.length = k ∧ ∀ v ∈ c, v < N
  | 0, c, h => by
    simp only [allLists, List.mem_singleton] at h
    subst h
    simp
  | k + 1, c, h => by
    simp only [allLists, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨a, ha, l, hl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mem_allLists hl
    refine ⟨by simp [h1], fun v hv => ?_⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ha
    · exact h2 v hv

theorem mem_partners {n : Nat} {x a : Array Nat} (h : a ∈ partners n x) :
    ∃ c ∈ allLists (2 ^ n) n, ord3V n c = true ∧ pre1 n x (linA n c) = true ∧ a = linA n c := by
  unfold partners at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, hs⟩ := h
  by_cases h1 : ord3V n c = true
  · by_cases h2 : pre1 n x (linA n c) = true
    · rw [if_pos h1, if_pos h2] at hs
      exact ⟨c, hc, h1, h2, (Option.some.inj hs).symm⟩
    · rw [if_pos h1, if_neg h2] at hs
      exact absurd hs (by simp)
  · rw [if_neg h1] at hs
    exact absurd hs (by simp)

theorem cand_of {m n : Nat} {R : Nat → Nat} {c x : List Nat}
    (h : (!ord3V n c || ((List.range m).any fun i => decC n (R i) == c) ||
      !pre1L n x c) = true)
    (h1 : ord3V n c = true) (h2 : pre1L n x c = true) :
    ∃ i < m, linA n (decC n (R i)) = linA n c := by
  rw [h1, h2] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_false, List.any_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i, hi, by rw [he]⟩

theorem good_decC (n v : Nat) : Good n (decC n v) := by
  intro u hu
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hu
  exact Nat.mod_lt _ (Nat.two_pow_pos n)

theorem good_of_lt {n : Nat} {c : List Nat} (h : ∀ v ∈ c, v < 2 ^ n) : Good n c := h

theorem hid4 : idA (2 ^ 4) = linA 4 (idL 4) := by decide +kernel

theorem hid3 : idA (2 ^ 3) = linA 3 (idL 3) := by decide +kernel

theorem good_x0c4 : Good 4 (x0c 4) := by
  intro v hv
  have e : x0c 4 = [2, 3, 4, 8] := by decide
  rw [e] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

theorem good_x0c3 : Good 3 (x0c 3) := by
  intro v hv
  have e : x0c 3 = [2, 3, 4] := by decide
  rw [e] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

theorem candL4_all : ∀ d < 16, candL4 d = true := by
  intro d hd
  interval_cases d
  exacts [candL40, candL41, candL42, candL43, candL44, candL45, candL46, candL47, candL48, candL49,
    candL410, candL411, candL412, candL413, candL414, candL415]

theorem mem_partners4 {a : Array Nat} (h : a ∈ partners 4 (x0 4)) : ∃ i < 144, a = P4 i := by
  obtain ⟨c, hc, h1, h2, rfl⟩ := mem_partners h
  obtain ⟨hl, hb⟩ := mem_allLists hc
  have h2' : pre1L 4 (x0c 4) c = true := by
    rw [← pre1_lin hid4 good_x0c4 (good_of_lt hb)]
    exact h2
  match c, hl with
  | [c0, c1, c2, c3], _ =>
    have hc := candL4_all c3 (hb c3 (by simp))
    unfold candL4 at hc
    have hc' := CFSG.Monster.B.Co2.allLt_iff.1 (CFSG.Monster.B.Co2.allLt_iff.1
      (CFSG.Monster.B.Co2.allLt_iff.1 hc c0 (hb c0 (by simp))) c1 (hb c1 (by simp))) c2
      (hb c2 (by simp))
    obtain ⟨i, hi, he⟩ := cand_of hc' h1 h2'
    exact ⟨i, hi, he.symm⟩

theorem mem_partners3 {a : Array Nat} (h : a ∈ partners 3 (x0 3)) : ∃ i < 24, a = P3 i := by
  obtain ⟨c, hc, h1, h2, rfl⟩ := mem_partners h
  obtain ⟨hl, hb⟩ := mem_allLists hc
  have h2' : pre1L 3 (x0c 3) c = true := by
    rw [← pre1_lin hid3 good_x0c3 (good_of_lt hb)]
    exact h2
  match c, hl with
  | [c0, c1, c2], _ =>
    have hc := candL3_ok
    unfold candL3 at hc
    have hc' := CFSG.Monster.B.Co2.allLt_iff.1 (CFSG.Monster.B.Co2.allLt_iff.1
      (CFSG.Monster.B.Co2.allLt_iff.1 hc c0 (hb c0 (by simp))) c1 (hb c1 (by simp))) c2
      (hb c2 (by simp))
    obtain ⟨i, hi, he⟩ := cand_of (R := fun i => WT (144 + i)) hc' h1 h2'
    exact ⟨i, hi, he.symm⟩

theorem or3_mono {a p s p' s' : Bool} (hp : p' = true → p = true) (hs : s' = true → s = true)
    (h : (a || p' || s') = true) : (a || p || s) = true := by
  revert hp hs h
  cases a <;> cases p <;> cases s <;> cases p' <;> cases s' <;> decide

theorem pairT_sound {N : Nat} {x a b : Array Nat} {r : Nat} (h : pairT N x a b r = true) :
    (!meet3 N x a b || ptOK N x a b || sameOK N x a b) = true := by
  unfold pairT at h
  refine or3_mono ?_ ?_ h
  · intro hp
    rw [Bool.and_eq_true] at hp
    have h1 := hp.2
    unfold ptW at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := h1
    unfold ptOK
    refine List.any_eq_true.2 ⟨_, mem_wordsUpTo (decW_length 2 (r / 4 % 8)), ?_⟩
    dsimp only
    rw [Bool.and_eq_true]
    refine ⟨h1, List.any_eq_true.2 ⟨_, mem_wordsUpTo (decW_length 2 (r / 32 % 8)), ?_⟩⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨h2, h3⟩, List.any_eq_true.2 ⟨_, mem_wordsUpTo (decW_length 2 (r / 256 % 8)), h4⟩⟩
  · intro hs
    rw [Bool.and_eq_true] at hs
    unfold sameOK
    exact List.any_eq_true.2 ⟨_, mem_wordsUpTo (decW_length 6 (r / 4)), hs.2⟩

theorem rowL4_all : ∀ i < 144, rowL4 i = true := by
  intro i hi
  interval_cases i
  exacts [rowL40, rowL41, rowL42, rowL43, rowL44, rowL45, rowL46, rowL47, rowL48, rowL49, rowL410,
    rowL411, rowL412, rowL413, rowL414, rowL415, rowL416, rowL417, rowL418, rowL419, rowL420,
    rowL421, rowL422, rowL423, rowL424, rowL425, rowL426, rowL427, rowL428, rowL429, rowL430,
    rowL431, rowL432, rowL433, rowL434, rowL435, rowL436, rowL437, rowL438, rowL439, rowL440,
    rowL441, rowL442, rowL443, rowL444, rowL445, rowL446, rowL447, rowL448, rowL449, rowL450,
    rowL451, rowL452, rowL453, rowL454, rowL455, rowL456, rowL457, rowL458, rowL459, rowL460,
    rowL461, rowL462, rowL463, rowL464, rowL465, rowL466, rowL467, rowL468, rowL469, rowL470,
    rowL471, rowL472, rowL473, rowL474, rowL475, rowL476, rowL477, rowL478, rowL479, rowL480,
    rowL481, rowL482, rowL483, rowL484, rowL485, rowL486, rowL487, rowL488, rowL489, rowL490,
    rowL491, rowL492, rowL493, rowL494, rowL495, rowL496, rowL497, rowL498, rowL499, rowL4100,
    rowL4101, rowL4102, rowL4103, rowL4104, rowL4105, rowL4106, rowL4107, rowL4108, rowL4109,
    rowL4110, rowL4111, rowL4112, rowL4113, rowL4114, rowL4115, rowL4116, rowL4117, rowL4118,
    rowL4119, rowL4120, rowL4121, rowL4122, rowL4123, rowL4124, rowL4125, rowL4126, rowL4127,
    rowL4128, rowL4129, rowL4130, rowL4131, rowL4132, rowL4133, rowL4134, rowL4135, rowL4136,
    rowL4137, rowL4138, rowL4139, rowL4140, rowL4141, rowL4142, rowL4143]

theorem rowL3_all : ∀ i < 24, rowL3 i = true := by
  intro i hi
  interval_cases i
  exacts [rowL30, rowL31, rowL32, rowL33, rowL34, rowL35, rowL36, rowL37, rowL38, rowL39, rowL310,
    rowL311, rowL312, rowL313, rowL314, rowL315, rowL316, rowL317, rowL318, rowL319, rowL320,
    rowL321, rowL322, rowL323]

theorem checkT4_ok : checkT 4 = true := by
  unfold checkT
  dsimp only
  refine List.all_eq_true.2 fun a ha => List.all_eq_true.2 fun b hb => ?_
  obtain ⟨i, hi, rfl⟩ := mem_partners4 ha
  obtain ⟨j, hj, rfl⟩ := mem_partners4 hb
  have h := rowL4_all i hi
  unfold rowL4 at h
  have hp := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [← pairT_lin hid4 good_x0c4 (good_decC 4 _) (good_decC 4 _)] at hp
  have e : linA 4 (x0c 4) = x0 4 := rfl
  rw [e] at hp
  exact pairT_sound hp

theorem checkT3_ok : checkT 3 = true := by
  unfold checkT
  dsimp only
  refine List.all_eq_true.2 fun a ha => List.all_eq_true.2 fun b hb => ?_
  obtain ⟨i, hi, rfl⟩ := mem_partners3 ha
  obtain ⟨j, hj, rfl⟩ := mem_partners3 hb
  have h := rowL3_all i hi
  unfold rowL3 at h
  have hp := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [← pairT_lin hid3 good_x0c3 (good_decC 3 _) (good_decC 3 _)] at hp
  have e : linA 3 (x0c 3) = x0 3 := rfl
  rw [e] at hp
  exact pairT_sound hp

theorem c7226 : CFSG.Quasithin.Asc81c.Pf.Check.checkT 4 = true ∧
    CFSG.Quasithin.Asc81c.Pf.Check.checkT 3 = true := ⟨checkT4_ok, checkT3_ok⟩

end CertificateChecks.KernelAsc81c

end
