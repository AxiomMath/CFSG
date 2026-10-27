module

public import Certificates.Kernel.Misc.Asc81c.Data
import Certificates.Kernel.Misc.Asc81c.Checks
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

theorem chunk4_all : ∀ d < 16, chunk4 d = true := by
  intro d hd
  interval_cases d
  exacts [chunk40, chunk41, chunk42, chunk43, chunk44, chunk45, chunk46, chunk47, chunk48, chunk49,
    chunk410, chunk411, chunk412, chunk413, chunk414, chunk415]

theorem chunk3_all : ∀ c < 8, chunk3 c = true := by
  intro c hc
  interval_cases c
  exacts [chunk30, chunk31, chunk32, chunk33, chunk34, chunk35, chunk36, chunk37]

theorem check4_ok : check4 = true := by
  unfold check4
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun a ha => CFSG.Monster.B.Co2.allLt_iff.2 fun b hb =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => CFSG.Monster.B.Co2.allLt_iff.2 fun d hd => ?_
  have h := chunk4_all d hd
  unfold chunk4 at h
  exact pairW_sound (CFSG.Monster.B.Co2.allLt_iff.1 (CFSG.Monster.B.Co2.allLt_iff.1
    (CFSG.Monster.B.Co2.allLt_iff.1 h a ha) b hb) c hc)

theorem check3_ok : check3 = true := by
  unfold check3
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun a ha => CFSG.Monster.B.Co2.allLt_iff.2 fun b hb =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => ?_
  have h := chunk3_all c hc
  unfold chunk3 at h
  exact pairW_sound (CFSG.Monster.B.Co2.allLt_iff.1 (CFSG.Monster.B.Co2.allLt_iff.1 h a ha) b hb)

theorem c7224 : CFSG.Quasithin.Asc81c.Pf.Check.check4 = true ∧
    CFSG.Quasithin.Asc81c.Pf.Check.check3 = true := ⟨check4_ok, check3_ok⟩

end CertificateChecks.KernelAsc81c

end
