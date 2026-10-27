module

public import Certificates.Kernel.He4049.G
public import Certificates.Kernel.He4049.E
public import Certificates.Kernel.He4049.I
public import Certificates.Kernel.He4049.R
public import Certificates.Kernel.He4049.P
public import Certificates.Kernel.He4049.S
public import Certificates.Kernel.He4049.One
public import Certificates.Kernel.E16.Hall
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He4049.H

open CFSG.KD.He4049 CFSG.KC.Kc3K CFSG.KC.Enum
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.A5.Kc3SporLine

@[expose, reducible] noncomputable def D : CFSG.KD.E16.Data where
  n := 8330
  w := 14
  m := 16383
  NN := 343
  NE := 1024
  M := 191
  R := 25
  e0 := 0
  TF := TF
  B := B
  gs := gs
  eu := eu
  ev := ev
  ky := ky
  iv := iv
  kv := kv
  tg := tg
  vu := vu
  vv := vv
  rt := rt
  cj := cj
  RI := RI
  FR := FR
  FL := FL
  FM := FM
  pr := pr
  ct := ct
  NB := NB
  NM := NM

theorem chunk {len : Nat} (hl : 0 < len) (i : Nat) :
    Nat.add (Nat.mul (i / len) len) (i % len) = i ∧ i % len < len := by
  refine ⟨?_, Nat.mod_lt _ hl⟩
  change i / len * len + i % len = i
  rw [Nat.mul_comm]
  exact Nat.div_add_mod i len

theorem checks : CFSG.KD.E16.Checks D where
  hB := by decide
  hn := by norm_num
  gs_lt := by decide
  e0_lt := by norm_num
  el := fun k hk => by
    change k < 1024 at hk
    have hc : k / 128 < 8 := by omega
    have h := CFSG.KD.He4049.E.all (k / 128) hc
    unfold famE at h
    have := List.all_eq_true.1 h (k % 128) (List.mem_range.2 (chunk (by norm_num) k).2)
    rwa [(chunk (by norm_num) k).1] at this
  ivc := fun i hi => by
    change i < 191 at hi
    have hc : i / 32 < 6 := by omega
    have h := CFSG.KD.He4049.I.all (i / 32) hc
    unfold famI at h
    have := List.all_eq_true.1 h (i % 32) (List.mem_range.2 (chunk (by norm_num) i).2)
    rw [(chunk (by norm_num) i).1] at this
    simpa [hi] using this
  rtc := fun ρ hρ => by
    change ρ < 25 at hρ
    have hc : ρ / 5 < 5 := by omega
    have h := CFSG.KD.He4049.R.all (ρ / 5) hc
    unfold famR at h
    have := List.all_eq_true.1 h (ρ % 5) (List.mem_range.2 (chunk (by norm_num) ρ).2)
    rwa [(chunk (by norm_num) ρ).1] at this
  prc := fun i hi => by
    change i < 191 at hi
    have hc : i / 16 < 12 := by omega
    have h := CFSG.KD.He4049.P.all (i / 16) hc
    unfold famP at h
    have := List.all_eq_true.1 h (i % 16) (List.mem_range.2 (chunk (by norm_num) i).2)
    rw [(chunk (by norm_num) i).1] at this
    simp only [hi, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    exact this.1
  nbc := fun i hi => by
    change i < 191 at hi
    have hc : i / 16 < 12 := by omega
    have h := CFSG.KD.He4049.P.all (i / 16) hc
    unfold famP at h
    have := List.all_eq_true.1 h (i % 16) (List.mem_range.2 (chunk (by norm_num) i).2)
    rw [(chunk (by norm_num) i).1] at this
    simp only [hi, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    exact this.2
  one := CFSG.KD.He4049.one
  dfs := fun i hi => by
    change i < 191 at hi
    have hc : i / 16 < 12 := by omega
    have h := CFSG.KD.He4049.S.all (i / 16) hc
    unfold famS at h
    refine dfsKR_spec h i ?_ ?_
    · change i / 16 * 16 ≤ i
      omega
    · change i < i / 16 * 16 + min 16 (191 - i / 16 * 16)
      omega

section Prefix

variable {Γ : Type} [Group Γ]

theorem getD_foldl_eltStep : ∀ (l : List (Nat × Nat)) (acc : Array Γ) {i : Nat}, i < acc.size →
    (l.foldl eltStep acc).getD i 1 = acc.getD i 1
  | [], _, _, _ => rfl
  | p :: l, acc, i, hi => by
    rw [List.foldl_cons, getD_foldl_eltStep l _ (by unfold eltStep; simp; omega)]
    exact getD_push_lt acc _ 1 hi

theorem size_foldl_eltStep : ∀ (l : List (Nat × Nat)) (acc : Array Γ),
    (l.foldl eltStep acc).size = acc.size + l.length
  | [], _ => rfl
  | p :: l, acc => by
    rw [List.foldl_cons, size_foldl_eltStep l, List.length_cons]
    simp [eltStep]
    omega

theorem progX_eq : progX = heProg ++ progX.drop 265 := by decide +kernel

theorem slpElts_heProg (a b : Γ) {j : Nat} (hj : j < heProg.length + 2) :
    (slpElts a b heProg).getD j 1 = G.E a b j := by
  unfold G.E slpElts
  rw [progX_eq, List.foldl_append, getD_foldl_eltStep (progX.drop 265) (heProg.foldl eltStep #[a, b])
    (by rw [size_foldl_eltStep]; simp; omega)]

end Prefix

section Group

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin 8330)]

@[expose] noncomputable def RX (a b : Γ) : Subgroup Γ := Subgroup.closure {y | y ∈ gs.map (G.E a b)}

theorem hall [Finite Γ] {a b : Γ} (hta : (tab 8330 a).toArray = TA)
    (htb : (tab 8330 b).toArray = TB) (hbase : ∀ g : Γ, (∀ p ∈ B, act 8330 g p = p) → g = 1) :
    ∀ F : Subgroup Γ, F ≤ RX a b → (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) → (∀ x ∈ F, x * x = 1) →
      Nat.card F = 16 → ¬ PairFibersAllowed (Fin 8330) F :=
  @CFSG.KD.E16.hall D Γ _ _ (G.E a b) _
    ⟨fun j hj p hp => G.act_node hta htb hj hp, hbase⟩ checks

end Group

end CFSG.KD.He4049.H

end
