module

public import Certificates.Kernel.Sporadic.J3K.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.Certificates.Kernel.Spor.PChainSound
import CFSG.Certificates.Kernel.Spor.PK.Basic
public import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3K

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.J3.Native

@[expose] noncomputable def j3MulK (X Y : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => j3VecK Y x :: ih) X

@[expose] noncomputable def j3PowK (d : Nat) (M : List Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat) (idRows d).toList (fun _ ih => j3MulK ih M)

theorem j3_foldl_xor_init (R : Nat → Nat) (v a b : Nat) (l : List Nat) :
    l.foldl (fun acc j => if v.testBit j then acc ^^^ R j else acc) (a ^^^ b) =
      a ^^^ l.foldl (fun acc j => if v.testBit j then acc ^^^ R j else acc) b := by
  induction l generalizing b with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    split
    · rw [Nat.xor_assoc, ih]
    · exact ih b

theorem j3_vecMulN_toArray (L : List Nat) (v : Nat) :
    vecMulN L.length L.toArray v = j3VecK L v := by
  unfold vecMulN
  induction L generalizing v with
  | nil => rfl
  | cons r L ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have e : ∀ acc j, (if v.testBit (j + 1) then acc ^^^ ((r :: L).toArray[j + 1]?.getD 0)
        else acc) = (if (v >>> 1).testBit j then acc ^^^ (L.toArray[j]?.getD 0) else acc) := by
      intro acc j
      simp [Nat.testBit_succ, Nat.shiftRight_one]
    simp only [e]
    have h0 : (if v.testBit 0 then 0 ^^^ ((r :: L).toArray[0]?.getD 0) else 0) =
        (if v.testBit 0 then r else 0) ^^^ 0 := by
      split <;> simp
    rw [h0, j3_foldl_xor_init, ih]
    have h1 : (if v.testBit 0 then r else 0) = Bool.rec 0 r (Nat.beq (Nat.land v 1) 1) := by
      have hm : Nat.land v 1 = v % 2 := Nat.and_one_is_mod v
      rw [hm, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> rw [h] <;> rfl
    rw [h1]
    rfl

theorem j3MulK_eq (X Y : List Nat) : j3MulK X Y = X.map (j3VecK Y) := by
  induction X with
  | nil => rfl
  | cons x X ih => exact congrArg (List.cons _) ih

theorem j3_mulRows_toArray (X L : List Nat) (d : Nat) (h : L.length = d) :
    mulRows d X.toArray L.toArray = (j3MulK X L).toArray := by
  subst h
  unfold mulRows
  rw [j3MulK_eq, List.map_toArray]
  congr 1
  exact List.map_congr_left fun v _ => j3_vecMulN_toArray L v

theorem j3_powRows_toArray (L : List Nat) (d : Nat) (h : L.length = d) (e : Nat) :
    powRows d L.toArray e = (j3PowK d L e).toArray := by
  induction e with
  | zero => exact (Array.toArray_toList (xs := idRows d)).symm
  | succ e ih => rw [powRows, ih, j3_mulRows_toArray _ _ _ h]; rfl

theorem j3_matOK_of (hA : RAL.length = 80) (hB : RBL.length = 80)
    (h : ((j3PowK 80 RAL 2).toArray == idRows 80 && (j3PowK 80 RBL 3).toArray == idRows 80 &&
      (j3PowK 80 (j3MulK RAL RBL) 19).toArray == idRows 80) = true) :
    matOK RAL.toArray RBL.toArray = true := by
  have hC : (j3MulK RAL RBL).length = 80 := by rw [j3MulK_eq, List.length_map, hA]
  unfold matOK
  rw [j3_powRows_toArray _ _ hA, j3_powRows_toArray _ _ hB, j3_mulRows_toArray _ _ _ hB,
    j3_powRows_toArray _ _ hC]
  exact h

@[expose] noncomputable def invHalfK (L : Nat → Nat → Nat) (n NL : Nat) : Bool :=
  allN (Nat.div NL (nat_lit 2)) fun j => allN n fun x =>
    strictB (L (Nat.mul (nat_lit 2) j) x) fun y =>
      bAnd(Nat.blt y n, Nat.beq (L (Nat.succ (Nat.mul (nat_lit 2) j)) y) x)

theorem lt_of_leftInv {f g : Nat → Nat} {n : Nat} (hf : ∀ x < n, f x < n)
    (hg : ∀ x < n, g (f x) = x) {x : Nat} (hx : x < n) : g x < n := by
  have hinj : Set.InjOn f (Finset.range n : Set Nat) := fun a ha b hb hab => by
    rw [← hg a (Finset.mem_range.1 ha), ← hg b (Finset.mem_range.1 hb), hab]
  have hsub : (Finset.range n).image f ⊆ Finset.range n := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (hf a (Finset.mem_range.1 ha))
  have heq : (Finset.range n).image f = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  have hm : x ∈ (Finset.range n).image f := by
    rw [heq]
    exact Finset.mem_range.2 hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hm
  rw [hg a (Finset.mem_range.1 ha)]
  exact Finset.mem_range.1 ha

theorem invK_of_invHalfK {L : Nat → Nat → Nat} {n NL : Nat} (h : invHalfK L n NL = true) :
    PC.invK L n NL = true := by
  have hs : ∀ j < NL / 2, ∀ x < n, L (2 * j) x < n ∧ L (2 * j + 1) (L (2 * j) x) = x := by
    intro j hj x hx
    have := PK.allN_iff.1 (PK.allN_iff.1 h j hj) x hx
    simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  unfold PC.invK
  refine PK.allN_iff.2 fun j hj => PK.allN_iff.2 fun x hx => ?_
  simp only [PK.strictB_eq, PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.mul_eq,
    Nat.succ_eq_add_one]
  exact ⟨(hs j hj x hx).1, lt_of_leftInv (fun y hy => (hs j hj y hy).1)
    (fun y hy => (hs j hj y hy).2) hx, (hs j hj x hx).2⟩

@[expose] noncomputable def invLH : Bool := invHalfK LJ (nat_lit 20520) (nat_lit 8)

theorem colChk_ok : colChk 2 = true ∧ colChk 3 = true := ⟨by quickRfl, by quickRfl⟩
theorem invAB_ok : invAB = true := by quickRfl
theorem bfs_ok : bfs = true := by quickRfl
theorem invLH_ok : invLH = true := by quickRfl
theorem invL_ok : invL = true := invK_of_invHalfK invLH_ok
theorem tree1_ok : tree1 = true := by quickRfl
theorem labOK_ok : labOK = true := by quickRfl
theorem der_ok : der = true := by quickRfl

theorem rowsA_eq : CFSG.KS.Raw.unpack 80 80 (CFSG.KS.SporSch.payRun 80 J3SeedA.chars 0 0 0) =
    RAL.toArray := by decide +kernel
theorem rowsB_eq : CFSG.KS.Raw.unpack 80 80 (CFSG.KS.SporSch.payRun 80 J3SeedB.chars 0 0 0) =
    RBL.toArray := by decide +kernel
theorem colsA_eq : CFSG.Sporadic.J3.Native.transposeRows 80 RAL.toArray = CAJ := by decide +kernel
theorem colsB_eq : CFSG.Sporadic.J3.Native.transposeRows 80 RBL.toArray = CBJ := by decide +kernel
theorem mat_ok : CFSG.Sporadic.J3.Native.matOK RAL.toArray RBL.toArray = true :=
  j3_matOK_of (by decide +kernel) (by decide +kernel) (by decide +kernel)

end CertificateChecks.KernelSpor.J3K


end
