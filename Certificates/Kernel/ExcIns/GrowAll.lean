module

public import CFSG.Certificates.Kernel.ExcIns.GrowSound
public import Certificates.Kernel.ExcIns.GrowChecks
public import Certificates.Kernel.ExcIns.GrowChecks5
public import Certificates.Kernel.ExcExt.Glue

public section

noncomputable section

namespace CFSG.ExcInsK

open CFSG.ExcExtK CFSG.StandardType.GGQ2Frame.ExcRaw

@[expose] def R0 (x : Fin 8) : ℕ := ln128 D0.R x.val

theorem hR0 (x : Fin 8) : R0 x < 2 ^ nroots 0 := repsOK_sound ch712571rp x.isLt

private theorem nr0 : D0.nr = 8 := Nat.eq_of_beq_eq_true ch712571nr
private theorem gm0 : D0.gm = 2 ^ 4 - 1 := Nat.eq_of_beq_eq_true ch712571gm
private theorem w0 : (81 : ℕ) = 3 ^ dim 0 := by decide
private theorem ng0 : 4 ≤ nroots 0 := by decide

def Pc0 (c : ℕ) : Prop := ∀ j : Root 0, c.testBit j.val = false → (tabsK 0 D.T0).adj[j.val]! &&& c ≠ 0 →
  ∃ y : Fin 8, ∃ w : List (Root 0), (∀ u ∈ w, u.val < 4) ∧
    Chk.growC (tabsK 0 D.T0) (dim 0) (nroots 0) (c ||| 1 <<< j.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 0 D.T0) (nroots 0) u.val acc) (ln128 D0.R y.val)

private theorem H0 (c : ℕ) (L : List (ℕ × List ℕ))
    (hL : recsK D.T0 D0.PL 81 D0.gm D0.R D0.nr true c L = true) : Pc0 c :=
  hGrow_of tabsOK_D0 w0 ch712571pl gm0 ng0 nr0 hL

private theorem all0 : ∀ x < 8, Pc0 (ln128 D0.R x) := by
  have h1 := forall_lt_succ (P := fun x => Pc0 (ln128 D0.R x)) (forall_lt_zero _) (H0 _ _ ch712571g_0)
  have h2 := forall_lt_succ h1 (H0 _ _ ch712571g_1)
  have h3 := forall_lt_succ h2 (H0 _ _ ch712571g_2)
  have h4 := forall_lt_succ h3 (H0 _ _ ch712571g_3)
  have h5 := forall_lt_succ h4 (H0 _ _ ch712571g_4)
  have h6 := forall_lt_succ h5 (H0 _ _ ch712571g_5)
  have h7 := forall_lt_succ h6 (H0 _ _ ch712571g_6)
  exact forall_lt_succ h7 (H0 _ _ ch712571g_7)

theorem hGrow0 (x : Fin 8) : ∀ j : Root 0, (R0 x).testBit j.val = false →
    (tabsK 0 D.T0).adj[j.val]! &&& R0 x ≠ 0 → ∃ y : Fin 8, ∃ w : List (Root 0), (∀ u ∈ w, u.val < 4) ∧
      Chk.growC (tabsK 0 D.T0) (dim 0) (nroots 0) (R0 x ||| 1 <<< j.val) =
        w.foldr (fun u acc => Chk.imgN (tabsK 0 D.T0) (nroots 0) u.val acc) (R0 y) :=
  all0 x.val x.isLt

theorem hSeed0 : ∀ i : Root 0, ∃ y : Fin 8, ∃ w : List (Root 0), (∀ u ∈ w, u.val < 4) ∧
    Chk.growC (tabsK 0 D.T0) (dim 0) (nroots 0) (1 <<< i.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 0 D.T0) (nroots 0) u.val acc) (R0 y) :=
  hSeed_of tabsOK_D0 w0 ch712571pl gm0 ng0 nr0 ch712571s

@[expose] def R2 (x : Fin 8) : ℕ := ln128 D2.R x.val

theorem hR2 (x : Fin 8) : R2 x < 2 ^ nroots 2 := repsOK_sound ch712574rp x.isLt

private theorem nr2 : D2.nr = 8 := Nat.eq_of_beq_eq_true ch712574nr
private theorem gm2 : D2.gm = 2 ^ 6 - 1 := Nat.eq_of_beq_eq_true ch712574gm
private theorem w2 : (729 : ℕ) = 3 ^ dim 2 := by decide
private theorem ng2 : 6 ≤ nroots 2 := by decide

def Pc2 (c : ℕ) : Prop := ∀ j : Root 2, c.testBit j.val = false → (tabsK 2 D.T2).adj[j.val]! &&& c ≠ 0 →
  ∃ y : Fin 8, ∃ w : List (Root 2), (∀ u ∈ w, u.val < 6) ∧
    Chk.growC (tabsK 2 D.T2) (dim 2) (nroots 2) (c ||| 1 <<< j.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 2 D.T2) (nroots 2) u.val acc) (ln128 D2.R y.val)

private theorem H2 (c : ℕ) (L : List (ℕ × List ℕ))
    (hL : recsK D.T2 D2.PL 729 D2.gm D2.R D2.nr true c L = true) : Pc2 c :=
  hGrow_of tabsOK_D2 w2 ch712574pl gm2 ng2 nr2 hL

private theorem all2 : ∀ x < 8, Pc2 (ln128 D2.R x) := by
  have h1 := forall_lt_succ (P := fun x => Pc2 (ln128 D2.R x)) (forall_lt_zero _) (H2 _ _ ch712574g_0)
  have h2 := forall_lt_succ h1 (H2 _ _ ch712574g_1)
  have h3 := forall_lt_succ h2 (H2 _ _ ch712574g_2)
  have h4 := forall_lt_succ h3 (H2 _ _ ch712574g_3)
  have h5 := forall_lt_succ h4 (H2 _ _ ch712574g_4)
  have h6 := forall_lt_succ h5 (H2 _ _ ch712574g_5)
  have h7 := forall_lt_succ h6 (H2 _ _ ch712574g_6)
  exact forall_lt_succ h7 (H2 _ _ ch712574g_7)

theorem hGrow2 (x : Fin 8) : ∀ j : Root 2, (R2 x).testBit j.val = false →
    (tabsK 2 D.T2).adj[j.val]! &&& R2 x ≠ 0 → ∃ y : Fin 8, ∃ w : List (Root 2), (∀ u ∈ w, u.val < 6) ∧
      Chk.growC (tabsK 2 D.T2) (dim 2) (nroots 2) (R2 x ||| 1 <<< j.val) =
        w.foldr (fun u acc => Chk.imgN (tabsK 2 D.T2) (nroots 2) u.val acc) (R2 y) :=
  all2 x.val x.isLt

theorem hSeed2 : ∀ i : Root 2, ∃ y : Fin 8, ∃ w : List (Root 2), (∀ u ∈ w, u.val < 6) ∧
    Chk.growC (tabsK 2 D.T2) (dim 2) (nroots 2) (1 <<< i.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 2 D.T2) (nroots 2) u.val acc) (R2 y) :=
  hSeed_of tabsOK_D2 w2 ch712574pl gm2 ng2 nr2 ch712574s

@[expose] def R3 (x : Fin 6) : ℕ := ln128 D3.R x.val

theorem hR3 (x : Fin 6) : R3 x < 2 ^ nroots 3 := repsOK_sound ch712575rp x.isLt

private theorem nr3 : D3.nr = 6 := Nat.eq_of_beq_eq_true ch712575nr
private theorem gm3 : D3.gm = 2 ^ 6 - 1 := Nat.eq_of_beq_eq_true ch712575gm
private theorem w3 : (243 : ℕ) = 3 ^ dim 3 := by decide
private theorem ng3 : 6 ≤ nroots 3 := by decide

def Pc3 (c : ℕ) : Prop := ∀ j : Root 3, c.testBit j.val = false → (tabsK 3 D.T3).adj[j.val]! &&& c ≠ 0 →
  ∃ y : Fin 6, ∃ w : List (Root 3), (∀ u ∈ w, u.val < 6) ∧
    Chk.growC (tabsK 3 D.T3) (dim 3) (nroots 3) (c ||| 1 <<< j.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 3 D.T3) (nroots 3) u.val acc) (ln128 D3.R y.val)

private theorem H3 (c : ℕ) (L : List (ℕ × List ℕ))
    (hL : recsK D.T3 D3.PL 243 D3.gm D3.R D3.nr true c L = true) : Pc3 c :=
  hGrow_of tabsOK_D3 w3 ch712575pl gm3 ng3 nr3 hL

private theorem all3 : ∀ x < 6, Pc3 (ln128 D3.R x) := by
  have h1 := forall_lt_succ (P := fun x => Pc3 (ln128 D3.R x)) (forall_lt_zero _) (H3 _ _ ch712575g_0)
  have h2 := forall_lt_succ h1 (H3 _ _ ch712575g_1)
  have h3 := forall_lt_succ h2 (H3 _ _ ch712575g_2)
  have h4 := forall_lt_succ h3 (H3 _ _ ch712575g_3)
  have h5 := forall_lt_succ h4 (H3 _ _ ch712575g_4)
  exact forall_lt_succ h5 (H3 _ _ ch712575g_5)

theorem hGrow3 (x : Fin 6) : ∀ j : Root 3, (R3 x).testBit j.val = false →
    (tabsK 3 D.T3).adj[j.val]! &&& R3 x ≠ 0 → ∃ y : Fin 6, ∃ w : List (Root 3), (∀ u ∈ w, u.val < 6) ∧
      Chk.growC (tabsK 3 D.T3) (dim 3) (nroots 3) (R3 x ||| 1 <<< j.val) =
        w.foldr (fun u acc => Chk.imgN (tabsK 3 D.T3) (nroots 3) u.val acc) (R3 y) :=
  all3 x.val x.isLt

theorem hSeed3 : ∀ i : Root 3, ∃ y : Fin 6, ∃ w : List (Root 3), (∀ u ∈ w, u.val < 6) ∧
    Chk.growC (tabsK 3 D.T3) (dim 3) (nroots 3) (1 <<< i.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 3 D.T3) (nroots 3) u.val acc) (R3 y) :=
  hSeed_of tabsOK_D3 w3 ch712575pl gm3 ng3 nr3 ch712575s

@[expose] def R4 (x : Fin 12) : ℕ := ln128 D4.R x.val

theorem hR4 (x : Fin 12) : R4 x < 2 ^ nroots 4 := repsOK_sound ch712572rp x.isLt

private theorem nr4 : D4.nr = 12 := Nat.eq_of_beq_eq_true ch712572nr
private theorem gm4 : D4.gm = 2 ^ 7 - 1 := Nat.eq_of_beq_eq_true ch712572gm
private theorem w4 : (2187 : ℕ) = 3 ^ dim 4 := by decide
private theorem ng4 : 7 ≤ nroots 4 := by decide

def Pc4 (c : ℕ) : Prop := ∀ j : Root 4, c.testBit j.val = false → (tabsK 4 D.T4).adj[j.val]! &&& c ≠ 0 →
  ∃ y : Fin 12, ∃ w : List (Root 4), (∀ u ∈ w, u.val < 7) ∧
    Chk.growC (tabsK 4 D.T4) (dim 4) (nroots 4) (c ||| 1 <<< j.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 4 D.T4) (nroots 4) u.val acc) (ln128 D4.R y.val)

private theorem H4 (c : ℕ) (L : List (ℕ × List ℕ))
    (hL : recsK D.T4 D4.PL 2187 D4.gm D4.R D4.nr true c L = true) : Pc4 c :=
  hGrow_of tabsOK_D4 w4 ch712572pl gm4 ng4 nr4 hL

private theorem all4 : ∀ x < 12, Pc4 (ln128 D4.R x) := by
  have h1 := forall_lt_succ (P := fun x => Pc4 (ln128 D4.R x)) (forall_lt_zero _) (H4 _ _ ch712572g_0)
  have h2 := forall_lt_succ h1 (H4 _ _ ch712572g_1)
  have h3 := forall_lt_succ h2 (H4 _ _ ch712572g_2)
  have h4 := forall_lt_succ h3 (H4 _ _ ch712572g_3)
  have h5 := forall_lt_succ h4 (H4 _ _ ch712572g_4)
  have h6 := forall_lt_succ h5 (H4 _ _ ch712572g_5)
  have h7 := forall_lt_succ h6 (H4 _ _ ch712572g_6)
  have h8 := forall_lt_succ h7 (H4 _ _ ch712572g_7)
  have h9 := forall_lt_succ h8 (H4 _ _ ch712572g_8)
  have h10 := forall_lt_succ h9 (H4 _ _ ch712572g_9)
  have h11 := forall_lt_succ h10 (H4 _ _ ch712572g_10)
  exact forall_lt_succ h11 (H4 _ _ ch712572g_11)

theorem hGrow4 (x : Fin 12) : ∀ j : Root 4, (R4 x).testBit j.val = false →
    (tabsK 4 D.T4).adj[j.val]! &&& R4 x ≠ 0 → ∃ y : Fin 12, ∃ w : List (Root 4), (∀ u ∈ w, u.val < 7) ∧
      Chk.growC (tabsK 4 D.T4) (dim 4) (nroots 4) (R4 x ||| 1 <<< j.val) =
        w.foldr (fun u acc => Chk.imgN (tabsK 4 D.T4) (nroots 4) u.val acc) (R4 y) :=
  all4 x.val x.isLt

theorem hSeed4 : ∀ i : Root 4, ∃ y : Fin 12, ∃ w : List (Root 4), (∀ u ∈ w, u.val < 7) ∧
    Chk.growC (tabsK 4 D.T4) (dim 4) (nroots 4) (1 <<< i.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 4 D.T4) (nroots 4) u.val acc) (R4 y) :=
  hSeed_of tabsOK_D4 w4 ch712572pl gm4 ng4 nr4 ch712572s

@[expose] def R5 (x : Fin 14) : ℕ := ln128 D5.R x.val

theorem hR5 (x : Fin 14) : R5 x < 2 ^ nroots 5 := repsOK_sound ch712573rp x.isLt

private theorem nr5 : D5.nr = 14 := Nat.eq_of_beq_eq_true ch712573nr
private theorem gm5 : D5.gm = 2 ^ 8 - 1 := Nat.eq_of_beq_eq_true ch712573gm
private theorem w5 : (6561 : ℕ) = 3 ^ dim 5 := by decide
private theorem ng5 : 8 ≤ nroots 5 := by decide

def Pc5 (c : ℕ) : Prop := ∀ j : Root 5, c.testBit j.val = false → (tabsK 5 D.T5).adj[j.val]! &&& c ≠ 0 →
  ∃ y : Fin 14, ∃ w : List (Root 5), (∀ u ∈ w, u.val < 8) ∧
    Chk.growC (tabsK 5 D.T5) (dim 5) (nroots 5) (c ||| 1 <<< j.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 5 D.T5) (nroots 5) u.val acc) (ln128 D5.R y.val)

private theorem H5 (c : ℕ) (L : List (ℕ × List ℕ))
    (hL : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true c L = true) : Pc5 c :=
  hGrow_of tabsOK_D5 w5 ch712573pl gm5 ng5 nr5 hL

private theorem all5 : ∀ x < 14, Pc5 (ln128 D5.R x) := by
  have h1 := forall_lt_succ (P := fun x => Pc5 (ln128 D5.R x)) (forall_lt_zero _) (H5 _ _ ch712573g_0)
  have h2 := forall_lt_succ h1 (H5 _ _ ch712573g_1)
  have h3 := forall_lt_succ h2 (H5 _ _ ch712573g_2)
  have h4 := forall_lt_succ h3 (H5 _ _ ch712573g_3)
  have h5 := forall_lt_succ h4 (H5 _ _ ch712573g_4)
  have h6 := forall_lt_succ h5 (H5 _ _ ch712573g_5)
  have h7 := forall_lt_succ h6 (H5 _ _ ch712573g_6)
  have h8 := forall_lt_succ h7 (H5 _ _ ch712573g_7)
  have h9 := forall_lt_succ h8 (H5 _ _ ch712573g_8)
  have h10 := forall_lt_succ h9 (H5 _ _ ch712573g_9)
  have h11 := forall_lt_succ h10 (H5 _ _ ch712573g_10)
  have h12 := forall_lt_succ h11 (H5 _ _ ch712573g_11)
  have h13 := forall_lt_succ h12 (H5 _ _ ch712573g_12)
  exact forall_lt_succ h13 (H5 _ _ ch712573g_13)

theorem hGrow5 (x : Fin 14) : ∀ j : Root 5, (R5 x).testBit j.val = false →
    (tabsK 5 D.T5).adj[j.val]! &&& R5 x ≠ 0 → ∃ y : Fin 14, ∃ w : List (Root 5), (∀ u ∈ w, u.val < 8) ∧
      Chk.growC (tabsK 5 D.T5) (dim 5) (nroots 5) (R5 x ||| 1 <<< j.val) =
        w.foldr (fun u acc => Chk.imgN (tabsK 5 D.T5) (nroots 5) u.val acc) (R5 y) :=
  all5 x.val x.isLt

theorem hSeed5 : ∀ i : Root 5, ∃ y : Fin 14, ∃ w : List (Root 5), (∀ u ∈ w, u.val < 8) ∧
    Chk.growC (tabsK 5 D.T5) (dim 5) (nroots 5) (1 <<< i.val) =
      w.foldr (fun u acc => Chk.imgN (tabsK 5 D.T5) (nroots 5) u.val acc) (R5 y) :=
  hSeed_of tabsOK_D5 w5 ch712573pl gm5 ng5 nr5 ch712573s

end CFSG.ExcInsK

end

end
