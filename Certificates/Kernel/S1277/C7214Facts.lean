module

public import Certificates.Kernel.S1277.C7214ChkA
public import Certificates.Kernel.S1277.C7214ChkB
public import Certificates.Kernel.S1277.C7214ChkC
public import Certificates.Kernel.S1277.C7214ChkD
public import Certificates.Kernel.S1277.NmFacts
public import CFSG.Certificates.Kernel.S1277K7214Sound

public section

namespace CFSG.KP.C7214

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KC.C7214 CFSG.KD.S1277Gm
  CFSG.KD.C7214 CFSG.KS.C7214 CFSG.KS.S1277Gm

theorem stab1_eq : stab1 = st1P.map B6.ofP := by
  have e : (fun g : B6 => g.app 1 == 1) = fun g => Nat.beq (appK g 1) 1 := by
    funext g
    rw [nbeq, appK_eq]
  have h : stab1 = (gm6P.map B6.ofP).filter fun g => Nat.beq (appK g 1) 1 := by
    rw [← e, ← CFSG.KP.S1277Gm.gm6_eq]
    rfl
  rw [h]
  exact eq_of_eqB6 _ _ ok4

theorem cancel_aux {G G' X Y : List B6} (hG : G = G') (h : G ++ X = G' ++ Y) : X = Y := by
  subst hG
  exact List.append_cancel_left h

theorem sig_eq : gm6.map (·.comp sig6) = (gm6P.map sigP).map B6.ofP :=
  cancel_aux CFSG.KP.S1277Gm.gm6_eq (CFSG.KP.S1277ML.nm6_eqP.trans List.map_append)

theorem mem_sig {y : B6} (hy : y ∈ nm6) (hn : y ∉ gm6) : y ∈ gm6.map (·.comp sig6) := by
  have hy' : y ∈ gm6 ++ gm6.map (·.comp sig6) := hy
  rcases List.mem_append.1 hy' with h | h
  · exact absurd h hn
  · exact h

theorem of_gm6 {f : List B6 → Bool} (h : f (gm6P.map B6.ofP) = true) : f gm6 = true := by
  rw [CFSG.KP.S1277Gm.gm6_eq]
  exact h

theorem of_nm6 {f : List B6 → Bool} (h : f ((gm6P ++ gm6P.map sigP).map B6.ofP) = true) :
    f nm6 = true := by
  rw [CFSG.KP.S1277ML.nm6_eqP]
  exact h

theorem of_st {f : List B6 → Bool} (h : f (st1P.map B6.ofP) = true) : f stab1 = true := by
  rw [stab1_eq]
  exact h

theorem of_sig {f : List B6 → Bool} (h : f ((gm6P.map sigP).map B6.ofP) = true) :
    f (gm6.map (·.comp sig6)) = true := by
  rw [sig_eq]
  exact h

theorem h16 : chk16 (gm6.map (·.comp sig6)) nm6 yb = true := by
  rw [sig_eq, CFSG.KP.S1277ML.nm6_eqP]
  exact ok16

theorem h24 : chk24 (gm6.map (·.comp sig6)) nm6 = true := by
  rw [sig_eq, CFSG.KP.S1277ML.nm6_eqP]
  exact ok24

theorem h26 : chk26 gm6 nm6 = true := by
  rw [CFSG.KP.S1277Gm.gm6_eq, CFSG.KP.S1277ML.nm6_eqP]
  exact ok26

theorem c4 : stab1.length = 60 := by
  rw [stab1_eq, List.length_map]
  rfl

theorem c20 : ∀ x ∈ l1s0p, ∀ y ∈ l1s0p, x.comp y ∈ l1s0p := by
  have h := soundCl _ _ ok20
  rw [prodK_eq] at h
  exact h

theorem c21 : ∀ x ∈ l2s0p, ∀ y ∈ l2s0p, x.comp y ∈ l2s0p := by
  have h := soundCl _ _ ok21
  rw [prodK_eq] at h
  exact h

theorem c22 : ∀ B ∈ l1s0p, (∀ D ∈ l1 ++ s0p, B.comp D = D.comp B) → B = B6.id ∨ B = i1 := by
  have h := soundZ _ _ _ ok22
  rw [prodK_eq, s0pK_eq] at h
  exact h

theorem c23 : ∀ B ∈ l2s0p, (∀ D ∈ l2 ++ s0p, B.comp D = D.comp B) → B = B6.id ∨ B = i2 := by
  have h := soundZ _ _ _ ok23
  rw [prodK_eq, s0pK_eq] at h
  exact h

theorem c28 : ∀ B ∈ nm6, B.pow 60 = B6.id := by
  intro B hB
  have hB' : B ∈ gm6 ++ gm6.map (·.comp sig6) := hB
  rcases List.mem_append.1 hB' with h | h
  · exact sound28 gm6 (of_gm6 (f := chk28) ok28a) B h
  · exact sound28 _ (of_sig (f := chk28) ok28b) B h

open Certificates in
open CFSG.Quasithin.H13.S127.Mod in
theorem cert :
    (∀ c ∈ oVecL, ∃ g ∈ gm6, g.app c = 1) ∧
    (∀ c ∈ List.range 64, c ≠ 0 → c ∉ oVecL → ∀ d ∈ p1c, d ≠ 0 → ∃ g ∈ gm6, g.app c = d) ∧
    ((gm6.filter (presv pt1)).length = 180) ∧
    (stab1.length = 60) ∧
    (∀ g ∈ gm6, presv pt1 g = true → blkC g = [1, 0, 0, 1] → g = B6.id) ∧
    (∀ g ∈ stab1, det2 g = 1) ∧
    (∀ c ∈ List.range 64, c ∉ pt1 →
      spanHas (pt1 ++ stab1.map (·.app c)) (List.range 64) = true) ∧
    (spanHas (stab1.flatMap fun g => (List.range 64).map fun c => c ^^^ g.app c)
      (List.range 64) = true) ∧
    (∀ g ∈ stab1, ∃ a ∈ stab1, ∃ b ∈ stab1, a.pow 3 = B6.id ∧ b.pow 3 = B6.id ∧
      g = a.comp b) ∧
    (∀ g ∈ stab1, ∃ a ∈ stab1, ∃ b ∈ stab1, g = ((a.comp b).comp (inv6 a)).comp (inv6 b)) ∧
    (∀ B ∈ nm6, B.comp B = B6.id → B ≠ B6.id → fixCount B ≤ 16) ∧
    (∀ B ∈ nm6, B.pow 15 = B6.id → B ≠ B6.id → fixCount B < 8) ∧
    (∀ B ∈ nm6, B.comp B = B6.id → B ≠ B6.id → 16 ≤ fixCount B →
      ∃ c ∈ oVecL, B.app c = c) ∧
    (∀ B ∈ gm6, B.comp B = B6.id → B ≠ B6.id →
      ∃ g ∈ gm6, ∀ c ∈ List.range 64, (B.app c = c ↔ g.app c ∈ l2c)) ∧
    (∀ B ∈ nm6, 8 ≤ (l2c.filter fun c => B.app c == c).length → B ∈ r2) ∧
    (∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id → ∀ B ∈ nm6,
      (∀ c ∈ List.range 64, y.app c = c → B.app c = c) → B = B6.id ∨ B = y) ∧
    (∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id → fixCount y = 8) ∧
    (∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id → ∀ p ∈ oPts, presv (ptOf p) y = true →
      ∃ c ∈ oVecL, y.app c = c) ∧
    (∀ τ ∈ nm6, τ ∉ gm6 → (∀ s ∈ s0, ∃ s' ∈ s0, τ.comp s = s'.comp τ) → two6 τ = true →
      ∃ k ∈ zs6, ∃ u ∈ s0p, k.comp τ = u.comp k) ∧
    (∀ x ∈ l1s0p, ∀ y ∈ l1s0p, x.comp y ∈ l1s0p) ∧
    (∀ x ∈ l2s0p, ∀ y ∈ l2s0p, x.comp y ∈ l2s0p) ∧
    (∀ B ∈ l1s0p, (∀ D ∈ l1 ++ s0p, B.comp D = D.comp B) → B = B6.id ∨ B = i1) ∧
    (∀ B ∈ l2s0p, (∀ D ∈ l2 ++ s0p, B.comp D = D.comp B) → B = B6.id ∨ B = i2) ∧
    (∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id →
      ∃ m ∈ nm6, y.comp m = m.comp i1 ∨ y.comp m = m.comp i2) ∧
    (∀ m ∈ nm6, i2.comp m ≠ m.comp i1) ∧
    (i1 ∈ nm6 ∧ i1 ∉ gm6 ∧ i2 ∈ nm6 ∧ i2 ∉ gm6) ∧
    (i1 ∈ l1s0p ∧ i2 ∈ l2s0p) ∧
    (∀ B ∈ nm6, B.pow 60 = B6.id) :=
  ⟨sound1 gm6 (of_gm6 (f := chk1) ok1),
    sound2 gm6 (of_gm6 (f := chk2) ok2),
    sound3 gm6 (of_gm6 (f := chk3) ok3),
    c4,
    sound5 gm6 (of_gm6 (f := chk5) ok5),
    sound6 stab1 (of_st (f := chk6) ok6),
    sound7 stab1 (of_st (f := chk7) ok7),
    sound8 stab1 (of_st (f := chk8) ok8),
    sound9 stab1 (of_st (f := chk9) ok9),
    sound10 stab1 w10 (of_st (f := fun T => chk10 T w10) ok10),
    sound11 nm6 (of_nm6 (f := chk11) ok11),
    sound12 nm6 (of_nm6 (f := chk12) ok12),
    sound13 nm6 (of_nm6 (f := chk13) ok13),
    sound14 gm6 (of_gm6 (f := chk14) ok14),
    sound15 nm6 (of_nm6 (f := chk15) ok15),
    fun y hy hn h1 => sound16 _ nm6 yb h16 y (mem_sig hy hn) h1,
    fun y hy hn => sound17 _ (of_sig (f := chk17) ok17) y (mem_sig hy hn),
    fun y hy hn => sound18 _ (of_sig (f := chk18) ok18) y (mem_sig hy hn),
    fun t ht hn => sound19 _ (of_sig (f := chk19) ok19) t (mem_sig ht hn),
    c20, c21, c22, c23,
    fun y hy hn h1 => sound24 _ nm6 h24 y (mem_sig hy hn) h1,
    sound25 nm6 (of_nm6 (f := chk25) ok25),
    sound26 gm6 nm6 h26,
    sound27 ok27,
    c28⟩

end CFSG.KP.C7214

end
