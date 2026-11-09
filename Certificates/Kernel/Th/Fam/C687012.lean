module

public import Certificates.Kernel.Th.Fam.K
public import Certificates.Data.Th687.MFactsB
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.MFactsBData

@[expose] def tT : TE := .word (wJ 6)

@[expose] noncomputable def centP (k : Fin 512) : Bool :=
  Nat.beq ((TE.mul tT (.nf k)).pk thK) ((TE.mul (.nf k) tT).pk thK)

@[expose] noncomputable def centL : List (Fin 512) := (List.finRange 512).filter centP

@[expose] noncomputable def centCK : Bool :=
  centL.all fun k => if k.val = 0 ∨ k.val = 1 then true else centL.any fun k' =>
    Nat.beq ((TE.mul (.nf k) (.nf k')).pk thK) ((TE.mul (.nf k') (.nf k)).pk thK) == false

@[expose] def centA687012 : List (Fin 512) := [0, 1, 52, 53, 72, 73, 124, 125]
@[expose] def centB687012 : List (Fin 512) := [146, 147, 166, 167, 218, 219, 238, 239]
@[expose] def centC687012 : List (Fin 512) := [276, 277, 288, 289, 348, 349, 360, 361]
@[expose] def centD687012 : List (Fin 512) := [390, 391, 434, 435, 462, 463, 506, 507]

@[expose] def centL687012 : List (Fin 512) :=
  centA687012 ++ centB687012 ++ centC687012 ++ centD687012

@[expose] def chunk687012 (p q : Fin 512 → Bool) (i : Nat) : Bool :=
  (List.finRange 512).all fun k => !(Nat.beq (k.val / 64) i) || (p k == q k)

theorem filter_chunk687012 (p q : Fin 512 → Bool) (h : ∀ i, i < 8 → chunk687012 p q i = true) :
    (List.finRange 512).filter p = (List.finRange 512).filter q := by
  refine List.filter_congr fun k hk => ?_
  have h1 := h (k.val / 64) (by omega)
  simp only [chunk687012, List.all_eq_true] at h1
  have h2 := h1 k hk
  rw [Nat.beq_refl] at h2
  simpa using h2

theorem all4_687012 {α : Type} (f : α → Bool) (a b c d : List α) (ha : a.all f = true)
    (hb : b.all f = true) (hc : c.all f = true) (hd : d.all f = true) :
    (a ++ b ++ c ++ d).all f = true := by
  simp [List.all_append, ha, hb, hc, hd]

theorem cent687012_0 : chunk687012 centP (centL687012.contains ·) 0 = true := by quickRfl
theorem cent687012_1 : chunk687012 centP (centL687012.contains ·) 1 = true := by quickRfl
theorem cent687012_2 : chunk687012 centP (centL687012.contains ·) 2 = true := by quickRfl
theorem cent687012_3 : chunk687012 centP (centL687012.contains ·) 3 = true := by quickRfl
theorem cent687012_4 : chunk687012 centP (centL687012.contains ·) 4 = true := by quickRfl
theorem cent687012_5 : chunk687012 centP (centL687012.contains ·) 5 = true := by quickRfl
theorem cent687012_6 : chunk687012 centP (centL687012.contains ·) 6 = true := by quickRfl
theorem cent687012_7 : chunk687012 centP (centL687012.contains ·) 7 = true := by quickRfl

theorem centRec687012 :
    ((List.finRange 512).filter (centL687012.contains ·) == centL687012) = true := by quickRfl

theorem centL_eq687012 : centL = centL687012 := by
  have h := filter_chunk687012 centP (centL687012.contains ·) fun i hi =>
    match i, hi with
    | 0, _ => cent687012_0
    | 1, _ => cent687012_1
    | 2, _ => cent687012_2
    | 3, _ => cent687012_3
    | 4, _ => cent687012_4
    | 5, _ => cent687012_5
    | 6, _ => cent687012_6
    | 7, _ => cent687012_7
    | _ + 8, h => absurd h (by omega)
  unfold centL
  rw [h]
  exact eq_of_beq centRec687012

theorem ok687012a : Nat.beq centL.length 32 = true := by
  rw [centL_eq687012]
  quickRfl

@[expose] noncomputable def nc687012 (k : Fin 512) : Bool :=
  if k.val = 0 ∨ k.val = 1 then true else centL687012.any fun k' =>
    Nat.beq ((TE.mul (.nf k) (.nf k')).pk thK) ((TE.mul (.nf k') (.nf k)).pk thK) == false

theorem nc687012_A : centA687012.all nc687012 = true := by quickRfl
theorem nc687012_B : centB687012.all nc687012 = true := by quickRfl
theorem nc687012_C : centC687012.all nc687012 = true := by quickRfl
theorem nc687012_D : centD687012.all nc687012 = true := by quickRfl

theorem ok687012b : centCK = true := by
  unfold centCK
  rw [centL_eq687012]
  exact all4_687012 nc687012 _ _ _ _ nc687012_A nc687012_B nc687012_C nc687012_D

end CertificateChecks.KernelTh.Fam

end
