module

public import Certificates.Kernel.Misc.Asc81c.Data
import Certificates.Kernel.Misc.Asc81c.Checks
public import Certificates.Kernel.Misc.Asc81c.LinSound
import CFSG.Monster.B.Co2.PermArr
import Mathlib.Tactic.IntervalCases
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check CFSG.Monster.B.Co2.Native CFSG.KGroups.Native

theorem mem_wordsOfLen : ∀ w : List Bool, w ∈ wordsOfLen w.length
  | [] => by simp [wordsOfLen]
  | b :: w => by
    simp only [List.length_cons, wordsOfLen, List.mem_flatMap]
    exact ⟨w, mem_wordsOfLen w, by cases b <;> simp⟩

theorem mem_wordsUpTo {w : List Bool} {L : Nat} (h : w.length ≤ L) : w ∈ wordsUpTo L := by
  unfold wordsUpTo
  exact List.mem_flatMap.2 ⟨w.length, List.mem_range.2 (by omega), mem_wordsOfLen w⟩

theorem decW_length : ∀ f v, (decW f v).length ≤ f
  | 0, _ => by simp [decW]
  | f + 1, v => by
    unfold decW
    split
    · simp
    · have := decW_length f (v / 2)
      simp only [List.length_cons]
      omega

theorem or_mono {a b c p g f p' g' f' : Bool} (hp : p' = true → p = true)
    (hg : g' = true → g = true) (hf : f' = true → f = true)
    (h : (a || (b || c || p' || g' || f')) = true) : (a || (b || c || p || g || f)) = true := by
  revert hp hg hf h
  cases a <;> cases b <;> cases c <;> cases p <;> cases g <;> cases f <;> cases p' <;> cases g' <;>
    cases f' <;> decide

theorem pairW_sound {n : Nat} {x : Array Nat} {c : List Nat} {r : Nat} (h : pairW n x c r = true) :
    pairOK n x c = true := by
  unfold pairW at h
  rw [ord3G_eq, linAG_eq] at h
  unfold pairOK
  dsimp only at h ⊢
  refine or_mono ?_ ?_ id h
  · intro hp
    rw [Bool.and_eq_true] at hp
    unfold plainOK
    exact List.any_eq_true.2 ⟨_, mem_wordsUpTo (decW_length 10 _), hp.2⟩
  · intro hg
    rw [Bool.and_eq_true] at hg
    have h1 := hg.2
    unfold genW genW2 at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := h1
    unfold genOK
    refine List.any_eq_true.2 ⟨_, mem_wordsUpTo (decW_length 4 (r / 4 % 32)), ?_⟩
    dsimp only
    rw [Bool.and_eq_true]
    refine ⟨h1, List.any_eq_true.2 ⟨_, mem_wordsUpTo (decW_length 4 (r / 128 % 32)), ?_⟩⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨h2, h3⟩, List.any_eq_true.2 ⟨_, mem_wordsUpTo (decW_length 4 (r / 4096 % 32)), h4⟩⟩

theorem chunkL4_all : ∀ d < 16, chunkL4 d = true := by
  intro d hd
  interval_cases d
  exacts [chunkL40, chunkL41, chunkL42, chunkL43, chunkL44, chunkL45, chunkL46, chunkL47, chunkL48,
    chunkL49, chunkL410, chunkL411, chunkL412, chunkL413, chunkL414, chunkL415]

theorem chunkL3_all : ∀ c < 8, chunkL3 c = true := by
  intro c hc
  interval_cases c
  exacts [chunkL30, chunkL31, chunkL32, chunkL33, chunkL34, chunkL35, chunkL36, chunkL37]

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

theorem goodL4 {a b c d : Nat} (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    Good 4 [a, b, c, d] := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> assumption

theorem goodL3 {a b c : Nat} (ha : a < 8) (hb : b < 8) (hc : c < 8) : Good 3 [a, b, c] := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem check4_ok : check4 = true := by
  unfold check4
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun a ha => CFSG.Monster.B.Co2.allLt_iff.2 fun b hb =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => CFSG.Monster.B.Co2.allLt_iff.2 fun d hd => ?_
  have h := chunkL4_all d hd
  unfold chunkL4 at h
  have h' := CFSG.Monster.B.Co2.allLt_iff.1 (CFSG.Monster.B.Co2.allLt_iff.1
    (CFSG.Monster.B.Co2.allLt_iff.1 h a ha) b hb) c hc
  rw [pairWL_eq hid4 good_x0c4 (goodL4 ha hb hc hd)] at h'
  exact pairW_sound h'

theorem check3_ok : check3 = true := by
  unfold check3
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun a ha => CFSG.Monster.B.Co2.allLt_iff.2 fun b hb =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => ?_
  have h := chunkL3_all c hc
  unfold chunkL3 at h
  have h' := CFSG.Monster.B.Co2.allLt_iff.1 (CFSG.Monster.B.Co2.allLt_iff.1 h a ha) b hb
  rw [pairWL_eq hid3 good_x0c3 (goodL3 ha hb hc)] at h'
  exact pairW_sound h'

theorem c7224 : CFSG.Quasithin.Asc81c.Pf.Check.check4 = true ∧
    CFSG.Quasithin.Asc81c.Pf.Check.check3 = true := ⟨check4_ok, check3_ok⟩

end CertificateChecks.KernelAsc81c

end
