module

public import Certificates.Kernel.Sporadic.Fi24F4.JT
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Mathlib.Data.Matrix.Mul

set_option Elab.async false

#kc_repo #kc_natLines CFSG.KD.Fi24F4.JXs fxD "Certificates/Kernel/Sporadic/Fi24F4/data/jx.txt" 184728 13568603482653193573

namespace CFSG.KD.Fi24F4.JXs

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24R2W CFSG.KC.Fi24F4J CFSG.KC.Fi24NetPt CFSG.KD.Fi24Net
  CFSG.KD.Fi24F4

noncomputable def itN (f : Nat → Nat) (m x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => f y) m

theorem itN_lt {f : Nat → Nat} (hf : ∀ x < 524288, f x < 524288) :
    ∀ m x, x < 524288 → itN f m x < 524288
  | 0, _, hx => hx
  | m + 1, x, hx => hf _ (itN_lt hf m x hx)

theorem repL_walk {u : List Nat} {f : Nat → Nat} (hu : ∀ x < 524288, walkN NW u.reverse x = f x)
    (hf : ∀ x < 524288, f x < 524288) :
    ∀ m x, x < 524288 → walkN NW (repL u m).reverse x = itN f m x
  | 0, _, _ => rfl
  | m + 1, x, hx => by
    change walkN NW (u ++ repL u m).reverse x = f (itN f m x)
    rw [List.reverse_append, walkN_append, repL_walk hu hf m x hx]
    exact hu _ (itN_lt hf m x hx)

theorem snc_of {k : Nat} (h : stY (nthW J.sn k) (gw ti (nW k)) = true) : snc k = true :=
  stage_cw h

theorem sqc_of {e : Nat}
    (h : stY (nthW J.sq e) (itN (gw tiQ (qW.getD e ([], 0)).1) (qW.getD e ([], 0)).2) = true) :
    sqc e = true := by
  unfold sqc
  refine stage_tab (fun x hx => ?_) h
  rw [cwQ_eq]
  exact repL_walk (fun y hy => gw_walk tiQ tiQ_lt _ y hy) (fun y hy => gw_lt tiQ _ y hy) _ x hx

noncomputable def fxRest (F : Nat → Nat) (P0 s k m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) s
    (fun j acc => strictN acc (fun a => Fi24FixP.fixStep F P0 (Nat.add k j) a)) m

theorem fxAcc_add (F : Nat → Nat) (P0 k : Nat) :
    ∀ m, Fi24FixP.fixAcc F P0 (Nat.add k m) = fxRest F P0 (Fi24FixP.fixAcc F P0 k) k m
  | 0 => rfl
  | m + 1 => by
    change strictN (Fi24FixP.fixAcc F P0 (Nat.add k m))
        (fun a => Fi24FixP.fixStep F P0 (Nat.add k m) a) =
      strictN (fxRest F P0 (Fi24FixP.fixAcc F P0 k) k m)
        (fun a => Fi24FixP.fixStep F P0 (Nat.add k m) a)
    rw [fxAcc_add F P0 k m]

theorem fxStrictN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

noncomputable abbrev jfxF : Nat → Nat := Fi24FixP.walkP (planeL NW) (nthW J.sx 0)

noncomputable def fxPA (A : Nat) : Bool :=
  Nat.beq (strictN (jfxF (Fi24FixP.idPl19 (nat_lit 0))) fun P0 =>
    Fi24FixP.fixAcc jfxF P0 (nat_lit 7)) A

noncomputable def fxPB (A B : Nat) : Bool :=
  Nat.beq (strictN (jfxF (Fi24FixP.idPl19 (nat_lit 0))) fun P0 =>
    fxRest jfxF P0 A (nat_lit 7) (nat_lit 6)) B

noncomputable def fxPC (B n : Nat) : Bool :=
  Nat.beq (popcount (strictN (jfxF (Fi24FixP.idPl19 (nat_lit 0))) fun P0 =>
    fxRest jfxF P0 B (nat_lit 13) (nat_lit 6)) (nat_lit 524288)) n

theorem fx_of3 {n A B : Nat} (h1 : fxPA A = true) (h2 : fxPB A B = true)
    (h3 : fxPC B n = true) : Fi24FixP.fixOK (planeL NW) (nthW J.sx 0) n = true := by
  unfold fxPA at h1
  unfold fxPB at h2
  unfold fxPC at h3
  rw [fxStrictN] at h1 h2 h3
  have e13 : Fi24FixP.fixAcc jfxF (jfxF (Fi24FixP.idPl19 (nat_lit 0))) (nat_lit 13) = B := by
    rw [fxAcc_add _ _ (nat_lit 7) (nat_lit 6), Nat.eq_of_beq_eq_true h1]
    exact Nat.eq_of_beq_eq_true h2
  have e19 : Fi24FixP.fixAcc jfxF (jfxF (Fi24FixP.idPl19 (nat_lit 0))) (nat_lit 19) =
      fxRest jfxF (jfxF (Fi24FixP.idPl19 (nat_lit 0))) B (nat_lit 13) (nat_lit 6) := by
    rw [fxAcc_add _ _ (nat_lit 13) (nat_lit 6), e13]
  change Nat.beq (popcount (strictN (jfxF (Fi24FixP.idPl19 (nat_lit 0))) fun P0 =>
    Fi24FixP.fixAcc jfxF P0 (nat_lit 19)) (nat_lit 524288)) n = true
  rw [fxStrictN, e19]
  exact h3

theorem jfxA : fxPA fxD.n0 = true := by quickRfl

theorem jfxB : fxPB fxD.n0 fxD.n1 = true := by quickRfl

theorem jfxC : fxPC fxD.n1 (nat_lit 3240) = true := by quickRfl

end CFSG.KD.Fi24F4.JXs

public section

#kc_slice_range CFSG.KD.Fi24F4.sxc CFSG.KD.Fi24F4.Ck.sxc 0 5
#kc_slice_range CFSG.KD.Fi24F4.cubec CFSG.KD.Fi24F4.Ck.cubec 0 5
#kc_slice_range CFSG.KD.Fi24F4.commc CFSG.KD.Fi24F4.Ck.commc 0 25
#kc_slice_range CFSG.KD.Fi24F4.relc CFSG.KD.Fi24F4.Ck.relc 0 10

namespace CFSG.KD.Fi24F4.Ck

theorem fix : CFSG.KD.Fi24F4.fixc = true := JXs.fx_of3 JXs.jfxA JXs.jfxB JXs.jfxC

theorem qne : CFSG.KD.Fi24F4.qnec = true := by quickRfl

theorem snc0 : CFSG.KD.Fi24F4.snc (nat_lit 0) = true := JXs.snc_of (by quickRfl)

theorem snc1 : CFSG.KD.Fi24F4.snc (nat_lit 1) = true := JXs.snc_of (by quickRfl)

theorem sqc0 : CFSG.KD.Fi24F4.sqc (nat_lit 0) = true := JXs.sqc_of (by quickRfl)

theorem sqc1 : CFSG.KD.Fi24F4.sqc (nat_lit 1) = true := JXs.sqc_of (by quickRfl)

theorem sqc2 : CFSG.KD.Fi24F4.sqc (nat_lit 2) = true := JXs.sqc_of (by quickRfl)

theorem sqc3 : CFSG.KD.Fi24F4.sqc (nat_lit 3) = true := JXs.sqc_of (by quickRfl)

theorem sqc4 : CFSG.KD.Fi24F4.sqc (nat_lit 4) = true := JXs.sqc_of (by quickRfl)

theorem sqc5 : CFSG.KD.Fi24F4.sqc (nat_lit 5) = true := JXs.sqc_of (by quickRfl)

theorem sqc6 : CFSG.KD.Fi24F4.sqc (nat_lit 6) = true := JXs.sqc_of (by quickRfl)

theorem sqc7 : CFSG.KD.Fi24F4.sqc (nat_lit 7) = true := JXs.sqc_of (by quickRfl)

theorem sqc8 : CFSG.KD.Fi24F4.sqc (nat_lit 8) = true := JXs.sqc_of (by quickRfl)

theorem sqc9 : CFSG.KD.Fi24F4.sqc (nat_lit 9) = true := JXs.sqc_of (by quickRfl)

theorem sqc10 : CFSG.KD.Fi24F4.sqc (nat_lit 10) = true := JXs.sqc_of (by quickRfl)

theorem sqc11 : CFSG.KD.Fi24F4.sqc (nat_lit 11) = true := JXs.sqc_of (by quickRfl)

theorem sqc12 : CFSG.KD.Fi24F4.sqc (nat_lit 12) = true := JXs.sqc_of (by quickRfl)

end CFSG.KD.Fi24F4.Ck

end
