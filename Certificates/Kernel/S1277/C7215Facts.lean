module

public import Certificates.Kernel.S1277.C7215ChkA
public import Certificates.Kernel.S1277.C7215ChkB1
public import Certificates.Kernel.S1277.C7215ChkB2
public import Certificates.Kernel.S1277.C7215ChkB3
public import Certificates.Kernel.S1277.C7215ChkC
public import Certificates.Kernel.S1277.C7215ChkD
public import Certificates.Kernel.S1277.NmFacts
public import CFSG.Certificates.Kernel.S1277K7215Sound

public section

namespace CFSG.KP.C7215

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KC.C7214 CFSG.KC.C7215
  CFSG.KD.S1277Gm CFSG.KD.C7215 CFSG.KS.C7214 CFSG.KS.C7215 CFSG.KS.S1277Gm

theorem gm6_valid : ∀ g ∈ gm6, g.Valid := by
  rw [CFSG.KP.S1277Gm.gm6_eq]
  intro g hg
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg
  exact valid_ofP p

theorem filter_eq (l : List ℕ) (P : List ℕ)
    (h : eqB6 ((gm6P.map B6.ofP).filter (presvK l)) P = true) :
    gm6.filter (presv l) = P.map B6.ofP := by
  have e : presv l = presvK l := funext fun B => (presvK_eq l B).symm
  rw [e, CFSG.KP.S1277Gm.gm6_eq]
  exact eq_of_eqB6 _ _ h

theorem p1_eq : gm6.filter (presv p1c) = p1P.map B6.ofP := filter_eq _ _ okP

theorem l2_eq : gm6.filter (presv l2c) = l2P.map B6.ofP := filter_eq _ _ okQ

theorem of_gm6 {f : List B6 → Bool} (h : f (gm6P.map B6.ofP) = true) : f gm6 = true := by
  rw [CFSG.KP.S1277Gm.gm6_eq]
  exact h

theorem of_nm6 {f : List B6 → Bool} (h : f ((gm6P ++ gm6P.map sigP).map B6.ofP) = true) :
    f nm6 = true := by
  rw [CFSG.KP.S1277ML.nm6_eqP]
  exact h

theorem of_p1 {f : List B6 → Bool} (h : f (p1P.map B6.ofP) = true) :
    f (gm6.filter (presv p1c)) = true := by
  rw [p1_eq]
  exact h

theorem of_l2 {f : List B6 → Bool} (h : f (l2P.map B6.ofP) = true) :
    f (gm6.filter (presv l2c)) = true := by
  rw [l2_eq]
  exact h

theorem dreps_split : dreps = dreps.take 9 ++ ((dreps.drop 9).take 9 ++ dreps.drop 18) := by
  rfl

theorem mem_split {r : Mc} (hr : r ∈ dreps) :
    r ∈ dreps.take 9 ∨ r ∈ (dreps.drop 9).take 9 ∨ r ∈ dreps.drop 18 := by
  rw [dreps_split] at hr
  simpa only [List.mem_append] using hr

theorem c11 : ∀ r ∈ dreps, presv p1c r.toB6 = false → presv l2c r.toB6 = false →
    genAll (s0m ++ [r]) = true := by
  intro r hr
  rcases mem_split hr with h | h | h
  · exact snd11 CFSG.KP.S1277Gm.gmList_eq ok11a r h
  · exact snd11 CFSG.KP.S1277Gm.gmList_eq ok11b r h
  · exact snd11 CFSG.KP.S1277Gm.gmList_eq ok11c r h

open Certificates in
open CFSG.Quasithin.H13.S127.Mod in
theorem cert :
    (∀ B ∈ gm6, (∀ D ∈ gm6, B.comp D = D.comp B) → B ∈ zs6) ∧
    (∀ g ∈ gm6, presv p1c g = true → ∀ r ∈ r1, (g.comp r).comp (inv6 g) ∈ r1) ∧
    (∀ u ∈ gm6, presv p1c u = true → two6 u = true → u ∉ r1 →
      ∃ g ∈ gm6, presv p1c g = true ∧ two6 (u.comp ((g.comp u).comp (inv6 g))) = false) ∧
    (∀ g ∈ gm6, presv l2c g = true → ∀ r ∈ r2, (g.comp r).comp (inv6 g) ∈ r2) ∧
    (∀ u ∈ gm6, presv l2c u = true → two6 u = true → u ∉ r2 →
      ∃ g ∈ gm6, presv l2c g = true ∧ two6 (u.comp ((g.comp u).comp (inv6 g))) = false) ∧
    (∀ p ∈ l2c, ∃ r ∈ r2, ∃ c ∈ List.range 64, ∃ r' ∈ r2, ∃ c' ∈ List.range 64,
      p = (c ^^^ r.app c) ^^^ (c' ^^^ r'.app c')) ∧
    (∀ p ∈ l2c, ∃ s ∈ s0, ∃ c ∈ List.range 64, c ^^^ s.app c = p) ∧
    (∀ c ∈ List.range 64, c ∉ p1c →
      spanHas (p1c ++ (gm6.filter (presv p1c)).map (·.app c)) (List.range 64) = true) ∧
    (∀ c ∈ p1c, c ≠ 0 → spanHas ((gm6.filter (presv p1c)).map (·.app c)) p1c = true) ∧
    (∀ g ∈ gmList, ∃ s ∈ s0m, ∃ s' ∈ s0m, (s.mul g).mul s' ∈ dreps ∧
      presv p1c ((s.mul g).mul s').toB6 = presv p1c g.toB6 ∧
      presv l2c ((s.mul g).mul s').toB6 = presv l2c g.toB6) ∧
    (∀ r ∈ dreps, presv p1c r.toB6 = false → presv l2c r.toB6 = false →
      genAll (s0m ++ [r]) = true) ∧
    (∀ r ∈ dreps, presv p1c r.toB6 = false → presv l2c r.toB6 = true →
      ∀ r' ∈ dreps, presv p1c r'.toB6 = true → presv l2c r'.toB6 = false →
        genAll (s0m ++ [r, r']) = true) ∧
    (∀ y ∈ gm6, presv p1c y = true → ord3 y = true → y ∈ zs6 ∨ y ∈ l1 ∨
      ∃ s ∈ s0, two6 (y.comp (inv6 ((s.comp y).comp (inv6 s)))) = false ∧
        two6 (y.comp ((s.comp y).comp (inv6 s))) = false) ∧
    (∀ u ∈ gm6, presv p1c u = true → two6 u = true → u ∉ l1 → ∀ y ∈ l1, ord3 y = true →
      two6 (u.comp ((y.comp u).comp (inv6 y))) = false ∨
        two6 (u.comp (((inv6 y).comp u).comp y)) = false) ∧
    (∀ g ∈ gm6, fixP1 g = true → g.pow 15 = B6.id → g ∈ l1) ∧
    (∀ y ∈ gm6, presv l2c y = true → ord3 y = true → y ∈ zs6 ∨ y ∈ l2 ∨
      ∃ s ∈ s0, two6 (y.comp (inv6 ((s.comp y).comp (inv6 s)))) = false ∧
        two6 (y.comp ((s.comp y).comp (inv6 s))) = false) ∧
    (∀ u ∈ gm6, presv l2c u = true → two6 u = true → u ∉ l2 → ∀ y ∈ l2, ord3 y = true →
      two6 (u.comp ((y.comp u).comp (inv6 y))) = false ∨
        two6 (u.comp (((inv6 y).comp u).comp y)) = false) ∧
    (∀ g ∈ gm6, onQuot g = true → g.pow 15 = B6.id → g ∈ l2) ∧
    (∀ g ∈ gm6, presv p1c g = true → g.pow 15 = B6.id → ∃ a ∈ l1, ∃ z ∈ zs6, g = a.comp z) ∧
    (∀ g ∈ gm6, presv p1c g = true → ∃ a ∈ l1, ∃ z ∈ zs6, g.comp g = a.comp z) ∧
    (∀ g ∈ gm6, presv l2c g = true → g.pow 15 = B6.id → ∃ a ∈ l2, ∃ z ∈ zs6, g = a.comp z) ∧
    (∀ g ∈ gm6, presv l2c g = true → ∃ a ∈ l2, ∃ z ∈ zs6, g.comp g = a.comp z) ∧
    (∀ c ∈ List.range 64, c ≠ 0 → c ∉ oVecL →
      ∀ g ∈ gm6, g.pow 5 = B6.id → g ≠ B6.id → g.app c ≠ c) ∧
    (∀ c ∈ oVecL, ∃ g ∈ gm6, g.pow 5 = B6.id ∧ g ≠ B6.id ∧ g.app c = c) ∧
    (∀ B ∈ nm6, (∀ p ∈ oPts, pn (B.app p) = p) → B ∈ zs6) :=
  ⟨snd1 gm6 (of_gm6 (f := ck1) ok1),
    sndN gm6 gm6_valid p1c r1 (of_p1 (f := fun F => ckN F r1) ok2),
    sndT gm6 gm6_valid p1c r1 (of_p1 (f := fun F => ckT F r1) ok3),
    sndN gm6 gm6_valid l2c r2 (of_l2 (f := fun F => ckN F r2) ok4),
    sndT gm6 gm6_valid l2c r2 (of_l2 (f := fun F => ckT F r2) ok5),
    snd6 ok6,
    snd7 ok7,
    snd8 _ (of_p1 (f := ck8) ok8),
    snd9 _ (of_p1 (f := ck9) ok9),
    snd10 CFSG.KP.S1277Gm.gmList_eq ok10,
    c11,
    snd12 CFSG.KP.S1277Gm.gmList_eq ok12,
    sndY gm6 gm6_valid p1c l1 (of_p1 (f := fun F => ckY F l1) ok13),
    sndU gm6 gm6_valid p1c l1 l1_valid (of_p1 (f := fun F => ckU F l1) ok14),
    sndO fixP1K fixP1 fixP1K_eq gm6 gm6_valid l1 (of_gm6 (f := fun G => ckO fixP1K G l1) ok15),
    sndY gm6 gm6_valid l2c l2 (of_l2 (f := fun F => ckY F l2) ok16),
    sndU gm6 gm6_valid l2c l2 l2_valid (of_l2 (f := fun F => ckU F l2) ok17),
    sndO onQuotK onQuot onQuotK_eq gm6 gm6_valid l2 (of_gm6 (f := fun G => ckO onQuotK G l2) ok18),
    sndZo gm6 gm6_valid p1c l1 (of_p1 (f := fun F => ckZo F l1) ok19),
    sndZs gm6 p1c l1 (of_p1 (f := fun F => ckZs F l1) ok20),
    sndZo gm6 gm6_valid l2c l2 (of_l2 (f := fun F => ckZo F l2) ok21),
    sndZs gm6 l2c l2 (of_l2 (f := fun F => ckZs F l2) ok22),
    snd23 gm6 gm6_valid (of_gm6 (f := ck23) ok23),
    snd24 gm6 gm6_valid (of_gm6 (f := ck24) ok24),
    snd25 nm6 (of_nm6 (f := ck25) ok25)⟩

end CFSG.KP.C7215

end
