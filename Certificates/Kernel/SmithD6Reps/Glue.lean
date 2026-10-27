module

public import Certificates.Kernel.SmithD6Reps.Checks
public import Certificates.Kernel.SmithD6Stab.Glue
public import Certificates.Kernel.SmithD6Wt.Math
import all Certificates.Data.SmithD6Model
import all Certificates.Data.SmithD6Facts

public section

namespace CertificateChecks.SmithD6Reps

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Reps
  CertificateChecks.SmithD6Stab

theorem d6r_mf7All_eq (n : Nat) (p : Nat → Bool) : mf7All n p = (List.range n).all p := by
  apply Bool.eq_iff_iff.2
  rw [d6s_mf7All_iff, List.all_eq_true]
  simp [List.mem_range]

theorem commL_eq (A B : Array Nat) : mf7Commute A B = commL A B := by
  unfold mf7Commute commL
  rw [d6r_mf7All_eq]

theorem braidL_eq (A B : Array Nat) : mf7Braid A B = braidL A B := by
  unfold mf7Braid braidL
  rw [d6r_mf7All_eq]

theorem dihL_eq (A B : Array Nat) : mf7Dih A B = dihL A B := by
  unfold mf7Dih dihL
  rw [d6r_mf7All_eq]

theorem kindL_eq (A B : Array Nat) : mf7KindOf A B = kindL A B := by
  unfold mf7KindOf kindL
  rw [commL_eq, braidL_eq]

theorem relL_eq (k : Nat) (A B : Array Nat) : mf7RelOf k A B = relL k A B := by
  rcases k with _ | _ | k <;> simp only [mf7RelOf, relL, commL_eq, braidL_eq, dihL_eq]

theorem spanOKL_eq (T : Array Nat) (D : Mf7Span) : mf7SpanOK T D = spanOKL T D := by
  unfold mf7SpanOK spanOKL
  simp only [d6r_mf7All_eq]

theorem tvCols_eq (k : Nat) : tvCols k = tvColsP (linePair k) := rfl

section Model

variable (hidx : ∀ x, wtIdx x < 75735 ↔ wtTree.memB x = true)
include hidx

theorem mf7IsWt_eq (v : Nat) : mf7IsWt v = KT.memB v wtTree := by
  unfold mf7IsWt
  by_cases h : wtIdx v < 75735
  · simp [h, mf7_wt_wtIdx v h, (hidx v).1 h]
  · have hb : KT.memB v wtTree = false := by
      cases hm : KT.memB v wtTree
      · rfl
      · exact absurd ((hidx v).2 hm) h
    simp [h, hb]

theorem intOKL_eq (A B : Array Nat) (Dl D0 : Mf7Span) :
    mf7IntOK A B Dl D0 = intOKL (fun v => KT.memB v wtTree) A B Dl D0 := by
  unfold mf7IntOK intOKL
  simp only [d6r_mf7All_eq, commL_eq, mf7IsWt_eq hidx]

end Model

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
include hK

theorem tvCols_zero : tvCols 0 = tvColsP (1, 2) := by
  rw [tvCols_eq, linePair_eq hK, key_zero]
  rfl

theorem tvCols_rep {c : Nat} (hc : c < 6) :
    tvCols mf7Reps[c]! = tvColsP (pairK (repKeys.getD c 0)) := by
  obtain ⟨-, hkey, -, -⟩ := rep_facts hK hc
  have hr : mf7Reps[c]! = repPos.getD c 0 := by
    obtain rfl | rfl | rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
      omega
    all_goals rfl
  rw [tvCols_eq, hr, linePair_eq hK, hkey]

theorem mf7ChkReps_of_pinned (hidx : ∀ x, wtIdx x < 75735 ↔ wtTree.memB x = true) :
    mf7ChkReps () = true := by
  have hk := reps_ok
  unfold repsL at hk
  unfold mf7ChkReps
  simp only [d6r_mf7All_eq, spanOKL_eq, kindL_eq, relL_eq, intOKL_eq hidx, tvCols_zero hK]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hk ⊢
  refine ⟨hk.1, fun c hc => ?_⟩
  have hkind : mf7RepKinds[c]! = repKindsL.getD c 0 := by
    obtain rfl | rfl | rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by
      omega
    all_goals rfl
  rw [tvCols_rep hK hc, hkind]
  exact hk.2 c hc

theorem e4f7ChkPlane_of_pinned
    (hwt : ∀ j (hj : j < J.wtC.flatten.length), wt j = J.wtC.flatten[j]) :
    e4f7ChkPlane () = true := by
  have hk := plane_ok
  unfold CFSG.KD.SmithD6Reps.planeL at hk
  have hw : ∀ j < 75735, wt j = J.wtC.flatten.getD j 0 := fun j hj => by
    have hj' : j < J.wtC.flatten.length := by rw [SmithD6Wt.wtC_flatten_length]; exact hj
    rw [hwt j hj', List.getD_eq_getElem _ _ hj']
  have h71 : wt e4f7FixIdx = J.wtC.flatten.getD 71 0 := hw 71 (by decide)
  have h39 : wt e4f7FixPre = J.wtC.flatten.getD 39 0 := hw 39 (by decide)
  unfold e4f7ChkPlane
  simp only [tvCols_zero hK, tvCols_rep hK (c := 4) (by decide), h71, h39]
  simp only [Bool.and_eq_true] at hk ⊢
  exact ⟨⟨⟨⟨by decide, by decide⟩, hk.1.1⟩, hk.1.2⟩, hk.2⟩

end Model

end CertificateChecks.SmithD6Reps

end
