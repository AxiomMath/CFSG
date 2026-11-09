module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Data
public import Certificates.Kernel.Sporadic.Fi24Kit.Split
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

public section

#kc_slice_range CFSG.KD.Fi24ThreeO.sp CFSG.KD.Fi24ThreeO.Ck.sp 2 4

namespace CFSG.KD.Fi24ThreeO.Ck

open CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KD.Fi24Kit.Split

theorem allL_append {α : Type} (f : α → Bool) (l₁ l₂ : List α) :
    allL f (l₁ ++ l₂) = andB (allL f l₁) (allL f l₂) := by
  induction l₁ with
  | nil =>
    show allL f l₂ = andB true (allL f l₂)
    cases allL f l₂ <;> rfl
  | cons a t ih =>
    change andB (f a) (allL f (t ++ l₂)) = andB (andB (f a) (allL f t)) (allL f l₂)
    rw [ih]
    cases f a <;> cases allL f t <;> cases allL f l₂ <;> rfl

theorem sp0 : CFSG.KD.Fi24ThreeO.sp (nat_lit 0) = true := by
  unfold CFSG.KD.Fi24ThreeO.sp sepOK
  rw [bitN_eq_bitC]
  quickRfl

theorem allL_split {α : Type} {f : α → Bool} {l : List α} (n : Nat)
    (h₁ : allL f (List.take n l) = true) (h₂ : allL f (List.drop n l) = true) : allL f l = true := by
  rw [← List.take_append_drop n l, allL_append, h₁, h₂]
  all_goals rfl

theorem nc0 : allL (fun g => andB (incL g.2) (ncL CFSG.KD.Fi24ThreeO.OL CFSG.KD.Fi24Kit.NT g.2))
    (List.take 40 (CFSG.KD.Fi24ThreeO.gq (nat_lit 1))) = true := by quickRfl

theorem nc1 : allL (fun g => andB (incL g.2) (ncL CFSG.KD.Fi24ThreeO.OL CFSG.KD.Fi24Kit.NT g.2))
    (List.take 40 (List.drop 40 (CFSG.KD.Fi24ThreeO.gq (nat_lit 1)))) = true := by quickRfl

theorem nc2 : allL (fun g => andB (incL g.2) (ncL CFSG.KD.Fi24ThreeO.OL CFSG.KD.Fi24Kit.NT g.2))
    (List.take 40 (List.drop 40 (List.drop 40 (CFSG.KD.Fi24ThreeO.gq (nat_lit 1))))) = true := by quickRfl

theorem nc3 : allL (fun g => andB (incL g.2) (ncL CFSG.KD.Fi24ThreeO.OL CFSG.KD.Fi24Kit.NT g.2))
    (List.take 40 (List.drop 40 (List.drop 40 (List.drop 40 (CFSG.KD.Fi24ThreeO.gq (nat_lit 1)))))) = true := by quickRfl

theorem nc4 : allL (fun g => andB (incL g.2) (ncL CFSG.KD.Fi24ThreeO.OL CFSG.KD.Fi24Kit.NT g.2))
    (List.drop 40 (List.drop 40 (List.drop 40 (List.drop 40 (CFSG.KD.Fi24ThreeO.gq (nat_lit 1)))))) = true := by quickRfl

theorem ncAll : allL (fun g => andB (incL g.2) (ncL CFSG.KD.Fi24ThreeO.OL CFSG.KD.Fi24Kit.NT g.2)) (CFSG.KD.Fi24ThreeO.gq (nat_lit 1)) = true :=
  allL_split 40 nc0 (allL_split 40 nc1 (allL_split 40 nc2 (allL_split 40 nc3 nc4)))

theorem sp1 : CFSG.KD.Fi24ThreeO.sp (nat_lit 1) = true := by
  unfold CFSG.KD.Fi24ThreeO.sp sepOK
  rw [bitN_eq_bitC, ncAll]
  quickRfl

end CFSG.KD.Fi24ThreeO.Ck

end
