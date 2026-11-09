module

public import Certificates.Data.Kernel.M24G.Orbits
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.LookPackData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.LookQ

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem lookW_eq_P {α : Type} [Inhabited α] {n w : Nat} {enc : α → Nat} {dec : Nat → α}
    {L : List α} {P : Nat} (h : packW w (L.map enc) = P) :
    lookW n w enc dec L = fun i => if i < n then dec (fieldW w P i) else L.getD i default := by
  funext i
  rw [lookW, h]

theorem natBEq_eq : (instBEqOfDecidableEq : BEq Nat) = ⟨Nat.beq⟩ := by
  have h : (fun a b : Nat => decide (a = b)) = Nat.beq := by
    funext a b
    cases h : Nat.beq a b
    · simp only [decide_eq_false_iff_not]
      exact Nat.ne_of_beq_eq_false h
    · simp only [decide_eq_true_eq]
      exact Nat.eq_of_beq_eq_true h
  change (⟨fun a b => decide (a = b)⟩ : BEq Nat) = _
  rw [h]

theorem testBit_foldl_or (q : Nat) : ∀ (L : List Nat) (m : Nat),
    (L.foldl (fun m x => m ||| (1 <<< x)) m).testBit q = (m.testBit q || L.contains q)
  | [], m => by simp
  | x :: L, m => by
    rw [List.foldl_cons, testBit_foldl_or q L, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.contains_cons, Bool.or_assoc]
    congr 2
    by_cases h : x = q
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem contains_eq_maskL (L : List Nat) (q : Nat) : L.contains q = (maskL L).testBit q := by
  rw [maskL, testBit_foldl_or]
  simp

theorem ptTL_eq : packW 72 (TL.map Native.key3) = ptTL := by decide +kernel

theorem ptTS_eq : packW 77 (TS.map (packW 11)) = ptTS := by decide +kernel

theorem ptSL_eq : packW 144 (SL.map (packW 24)) = ptSL := by decide +kernel

end CFSG.KC.M24G.LookQ
