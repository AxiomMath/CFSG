module

public import CFSG.Monster.Existence.StdOdd.P5Inputs
public import Certificates.Data.Kernel.WeylE6
public import CFSG.Certificates.Kernel.Common.HexNat
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5 CFSG.KC.WeylE6

@[expose] def TBText : String := include_str "p5tb.hex"

@[expose] def STText : String := include_str "p5st.hex"

@[expose] noncomputable def TB : Nat := by hex_nat TBText 13122 13045430526525411810

@[expose] noncomputable def ST : Nat := by hex_nat STText 647 17782754877012980004

@[expose] def fin81 (n : Nat) : Fin 81 := ⟨n % 81, Nat.mod_lt _ (by decide)⟩

@[expose] def fin2 (n : Nat) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by decide)⟩

@[expose] noncomputable def raF (i : Fin 81) : Fin 81 := fin81 (f8 ST i.val)

@[expose] noncomputable def rbF (i : Fin 81) : Fin 81 := fin81 (f8 ST (81 + i.val))

@[expose] noncomputable def parF (j : Fin 81) : Fin 81 := fin81 (f8 ST (162 + j.val))

@[expose] noncomputable def lastF (j : Fin 81) : Fin 2 := fin2 (f8 ST (243 + j.val))

@[expose] noncomputable def stepF (c : Fin 2) (i : Fin 81) : Fin 81 := if c = 0 then raF i else rbF i

@[expose] noncomputable def tbF (i j : Fin 81) : Fin 81 := fin81 (f8 TB (81 * i.val + j.val))

theorem ra_eq : ∀ i : Fin 81, ra i = raF i := by decide +kernel

theorem rb_eq : ∀ i : Fin 81, rb i = rbF i := by decide +kernel

theorem pw_zero : pw 0 = [] := by decide +kernel

theorem pw_eq : ∀ j : Fin 81, 0 < j.val → parF j < j ∧ pw j = pw (parF j) ++ [lastF j] := by
  decide +kernel

theorem tb_rows : ∀ i j : Fin 81,
    (j.val = 0 → tbF i j = i) ∧ (0 < j.val → tbF i j = stepF (lastF j) (tbF i (parF j))) := by
  decide +kernel

theorem walk_append (w : List (Fin 2)) (c : Fin 2) (i : Fin 81) :
    walk (w ++ [c]) i = step c (walk w i) := by
  induction w generalizing i with
  | nil => rfl
  | cons d w ih => exact ih (step d i)

theorem step_eq (c : Fin 2) (i : Fin 81) : step c i = stepF c i := by
  simp only [step, stepF, ra_eq, rb_eq]

theorem walk_pw_tbF (i : Fin 81) : ∀ n (j : Fin 81), j.val = n → walk (pw j) i = tbF i j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hjn
    rcases Nat.eq_zero_or_pos j.val with h | h
    · have hj : j = 0 := Fin.ext h
      subst hj
      rw [pw_zero, (tb_rows i 0).1 rfl]
      rfl
    · obtain ⟨hp, hw⟩ := pw_eq j h
      rw [hw, walk_append, ih _ (hjn ▸ hp) _ rfl, step_eq, (tb_rows i j).2 h]

theorem tb_walk (i j : Fin 81) : tb i j = walk (pw j) i := by
  have h : 81 * i.val + j.val < 6561 := by omega
  have h1 : (81 * i.val + j.val) / 81 = i.val := by omega
  have h2 : (81 * i.val + j.val) % 81 = j.val := by omega
  simp only [tb, tbArr, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h, h1, h2, tbRaw]
  simp

theorem tb_eq_tbF : tb = tbF := funext fun i => funext fun j => by
  rw [tb_walk, walk_pw_tbF i j.val j rfl]

end CertificateChecks.MonsterExist.P5

end
