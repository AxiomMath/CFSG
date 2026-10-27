module

public import Certificates.Kernel.FzUT.BAssoc
public import Certificates.Kernel.FzUT.BFactsGlue
public import CFSG.Certificates.Kernel.FzUT.Codes

public section

namespace CFSG.KC.FzBMod

open Certificates.FzBU CFSG.OddStandard.SmallF3.FritzII

private theorem B {n m : Nat} (h : Nat.beq n m = true) : n = m := Nat.eq_of_beq_eq_true h

theorem uMulP_lt {x y : Nat} (hx : x < 64) (hy : y < 64) : uMulP x y < 64 := by
  rw [uMulP_eq hx hy]
  exact fzb_uMul_lt hx hy

private theorem pmulP_assoc {a b d : Nat} (ha : a < 64) (hb : b < 64) (hd : d < 64) :
    FzUT.pmulP (FzUT.pmulP a b) d = FzUT.pmulP a (FzUT.pmulP b d) := by
  have e : ∀ n < 64, FzUT.enc (FzUT.dec n) = n := fun n hn => FzUT.enc_dec ⟨n, hn⟩
  rw [← e a ha, ← e b hb, ← e d hd, FzUT.pmulP_eq, FzUT.pmulP_eq, FzUT.pmulP_eq, FzUT.pmulP_eq,
    mul_assoc]

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h (by simp)
  · exact ⟨rfl, h⟩

theorem rho_rho {x : Nat} (hx : x < 64) : rhoC (rhoC x) = x :=
  B (bAnd_true ((allN_iff 64 _).mp ch441796_rho x hx)).1

theorem rho_lt {x : Nat} (hx : x < 64) : rhoC x < 64 := by
  simpa [Nat.blt_eq] using (bAnd_true ((allN_iff 64 _).mp ch441796_rho x hx)).2

theorem rho_mul {x y : Nat} (hx : x < 64) (hy : y < 64) :
    rhoC (uMulP x y) = FzUT.pmulP (rhoC x) (rhoC y) :=
  B ((allN_iff 64 _).mp ((allN_iff 64 _).mp ch441796_rhoMul x hx) y hy)

theorem uMulP_assoc {a b d : Nat} (ha : a < 64) (hb : b < 64) (hd : d < 64) :
    uMulP (uMulP a b) d = uMulP a (uMulP b d) := by
  have h1 : rhoC (uMulP (uMulP a b) d) = rhoC (uMulP a (uMulP b d)) := by
    rw [rho_mul (uMulP_lt ha hb) hd, rho_mul ha hb, rho_mul ha (uMulP_lt hb hd), rho_mul hb hd,
      pmulP_assoc (rho_lt ha) (rho_lt hb) (rho_lt hd)]
  rw [← rho_rho (uMulP_lt (uMulP_lt ha hb) hd), h1, rho_rho (uMulP_lt ha (uMulP_lt hb hd))]

private theorem tab_hom {T : Nat} (h : tabHomB T = true) {a b : Nat} (ha : a < 64) (hb : b < 64) :
    lk6 T (uMulP a b) = uMulP (lk6 T a) (lk6 T b) :=
  B ((allN_iff 64 _).mp ((allN_iff 64 _).mp h a ha) b hb)

private theorem itN_hom {F : Nat → Nat} (hF : ∀ x, F x < 64)
    (hm : ∀ a < 64, ∀ b < 64, F (uMulP a b) = uMulP (F a) (F b)) (k : Nat) {a b : Nat}
    (ha : a < 64) (hb : b < 64) : itN F k (uMulP a b) = uMulP (itN F k a) (itN F k b) := by
  have hlt : ∀ k x, x < 64 → itN F k x < 64 := fun k x hx => by
    cases k with
    | zero => exact hx
    | succ k => exact hF _
  induction k with
  | zero => rfl
  | succ k ih =>
    change F (itN F k (uMulP a b)) = uMulP (F (itN F k a)) (F (itN F k b))
    rw [ih, hm _ (hlt k a ha) _ (hlt k b hb)]

private theorem itN_lt {F : Nat → Nat} (hF : ∀ x, F x < 64) (k : Nat) {x : Nat} (hx : x < 64) :
    itN F k x < 64 := by
  cases k with
  | zero => exact hx
  | succ k => exact hF _

theorem actL_mul (c : Bool) {w a b : Nat} (hw : w < 16) (ha : a < 64) (hb : b < 64) :
    actL c w (uMulP a b) = uMulP (actL c w a) (actL c w b) := by
  have hact : ∀ u < 64, actL c w u =
      itN (lk6 (tqT c)) (w % 4) (itN (lk6 (tsT c)) (w / 4 % 2) (itN (lk6 (tyT c)) (w / 8) u)) :=
    fun u hu => B ((allN_iff 64 _).mp ((allN_iff 16 _).mp (ch441796_act c) w hw) u hu)
  have hq := fun a (ha : a < 64) b (hb : b < 64) => tab_hom (ch441796_homQ c) ha hb
  have hs := fun a (ha : a < 64) b (hb : b < 64) => tab_hom (ch441796_homS c) ha hb
  have hy := fun a (ha : a < 64) b (hb : b < 64) => tab_hom (ch441796_homY c) ha hb
  have L := lk6_lt
  rw [hact _ (uMulP_lt ha hb), hact a ha, hact b hb, itN_hom (L _) hy _ ha hb,
    itN_hom (L _) hs _ (itN_lt (L _) _ ha) (itN_lt (L _) _ hb),
    itN_hom (L _) hq _ (itN_lt (L _) _ (itN_lt (L _) _ ha)) (itN_lt (L _) _ (itN_lt (L _) _ hb))]

theorem actL_comp (c : Bool) {w v u : Nat} (hw : w < 16) (hv : v < 16) (hu : u < 64) :
    actL c (amulL w v) u = actL c w (actL c v u) :=
  B ((allN_iff 64 _).mp ((allN_iff 16 _).mp ((allN_iff 16 _).mp (ch441796_actComp c) w hw) v hv) u hu)

theorem amulL_assoc {w v t : Nat} (hw : w < 16) (hv : v < 16) (ht : t < 16) :
    amulL (amulL w v) t = amulL w (amulL v t) :=
  B ((allN_iff 16 _).mp ((allN_iff 16 _).mp ((allN_iff 16 _).mp ch441796_amAssoc w hw) v hv) t ht)

theorem mulN_eq_split (c : Bool) (x y : Nat) :
    mulN c x y = uMulP (x % 64) (actL c (x / 64) (y % 64)) + 64 * amulL (x / 64) (y / 64) := by
  have e1 : ∀ z : Nat, Nat.land z 63 = z % 64 := fun z => by
    have h := Nat.and_two_pow_sub_one_eq_mod z 6
    norm_num at h
    exact h
  have e2 : ∀ z : Nat, Nat.shiftRight z 6 = z / 64 := fun z => by
    have h := Nat.shiftRight_eq_div_pow z 6
    norm_num at h
    exact h
  have e3 : ∀ z : Nat, Nat.shiftLeft z 6 = 64 * z := fun z => by
    have h := Nat.shiftLeft_eq z 6
    norm_num at h
    rw [Nat.mul_comm]
    exact h
  change Nat.add (uMulP (Nat.land x 63) (actL c (Nat.shiftRight x 6) (Nat.land y 63)))
    (Nat.shiftLeft (amulL (Nat.shiftRight x 6) (Nat.shiftRight y 6)) 6) = _
  rw [e1, e1, e2, e2, e3, Nat.add_eq]

theorem mulN_mod (c : Bool) (x y : Nat) :
    mulN c x y % 64 = uMulP (x % 64) (actL c (x / 64) (y % 64)) := by
  have h := uMulP_lt (Nat.mod_lt x (by norm_num)) (actL_lt c (x / 64) (y % 64))
  rw [mulN_eq_split]
  omega

theorem mulN_assoc (c : Bool) {x y z : Nat} (hx : x < 1024) (hy : y < 1024) (hz : z < 1024) :
    mulN c (mulN c x y) z = mulN c x (mulN c y z) := by
  have hxw : x / 64 < 16 := by omega
  have hyw : y / 64 < 16 := by omega
  have hzw : z / 64 < 16 := by omega
  have m64 : ∀ n : Nat, n % 64 < 64 := fun n => Nat.mod_lt n (by norm_num)
  rw [mulN_eq_split c (mulN c x y), mulN_eq_split c x (mulN c y z), mulN_mod, mulN_div, mulN_mod,
    mulN_div, amulL_assoc hxw hyw hzw, actL_mul c hxw (m64 y) (actL_lt _ _ _),
    ← actL_comp c hxw hyw (m64 z),
    uMulP_assoc (m64 x) (actL_lt _ _ _) (actL_lt _ _ _)]

private theorem id_facts (c : Bool) {x : Nat} (hx : x < 1024) :
    actL c 0 (x % 64) = x % 64 ∧ uMulP 0 (x % 64) = x % 64 ∧ uMulP (x % 64) 0 = x % 64 ∧
      actL c (x / 64) 0 = 0 ∧ amulL 0 (x / 64) = x / 64 ∧ amulL (x / 64) 0 = x / 64 := by
  have h := ch441796_id c
  simp only [idB, Bool.and_eq_true] at h
  obtain ⟨a1, h1⟩ := bAnd_true ((allN_iff 64 _).mp h.1 (x % 64) (Nat.mod_lt x (by norm_num)))
  obtain ⟨a2, a3⟩ := bAnd_true h1
  obtain ⟨b1, h2⟩ := bAnd_true ((allN_iff 16 _).mp h.2 (x / 64) (by omega))
  obtain ⟨b2, b3⟩ := bAnd_true h2
  exact ⟨B a1, B a2, B a3, B b1, B b2, B b3⟩

theorem mulN_zero_left (c : Bool) {x : Nat} (hx : x < 1024) : mulN c 0 x = x := by
  obtain ⟨a1, a2, -, -, b2, -⟩ := id_facts c hx
  rw [mulN_eq_split, Nat.zero_mod, Nat.zero_div, a1, a2, b2]
  omega

theorem mulN_zero_right (c : Bool) {x : Nat} (hx : x < 1024) : mulN c x 0 = x := by
  obtain ⟨-, -, a3, b1, -, b3⟩ := id_facts c hx
  rw [mulN_eq_split, Nat.zero_mod, Nat.zero_div, b1, a3, b3]
  omega

end CFSG.KC.FzBMod
