module

public import Certificates.Data.Kernel.O8.Dict3851
public import Certificates.Kernel.OmegaEight.SM3870
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitSylowData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitBits

public section

namespace CertificateChecks.KernelO8.Dict

open CFSG.KLie.CT CFSG.KC.O8D CFSG.EvenSmallLie.OmegaEight.NSplit
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SpBranch
  CertificateChecks.KernelO8 CertificateChecks.KernelO8.SM3870

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem allN_true (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyN_true (n : Nat) (f : Nat → Bool) : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero =>
    have e : anyN 0 f = false := rfl
    rw [e]
    exact ⟨fun h => absurd h (by decide), fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    change orB (f n) (anyN n f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

@[expose] noncomputable def blk (k : Nat) (f : Nat → Bool) : Bool :=
  allN (nat_lit 64) fun j => f (Nat.add (Nat.mul (nat_lit 64) k) j)

theorem of_blk {f : Nat → Bool} (h : ∀ k < 8, blk k f = true) : ∀ i < 512, f i = true := by
  intro i hi
  have := (allN_true _ _).1 (h (i / 64) (by omega)) (i % 64) (Nat.mod_lt _ (by decide))
  rwa [Nat.add_eq, Nat.mul_eq, Nat.div_add_mod] at this

theorem bit_eq (X i : Nat) : bit X i = X.testBit i := by
  have e : Nat.land (Nat.shiftRight X i) 1 = (X >>> i) % 2 := Nat.and_one_is_mod _
  have e2 : X.testBit i = decide ((X >>> i) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  unfold bit
  rw [e, e2]
  exact Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, decide_eq_true_iff])

theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem testBit_orN {n : Nat} {f : Nat → Nat} {j : Nat} :
    (orN n fun i => pw2 (f i)).testBit j = true ↔ ∃ i < n, f i = j := by
  induction n with
  | zero =>
    change Nat.testBit 0 j = true ↔ _
    simp
  | succ n ih =>
    change ((pw2 (f n)) ||| orN n fun i => pw2 (f i)).testBit j = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, pw2_eq, Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact Or.inr ⟨i, h, rfl⟩
      · exact Or.inl rfl

theorem sumN_eq (n : Nat) (g : Nat → Nat) : sumN n g = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => rw [Finset.sum_range_zero]; rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact Nat.add_comm _ _

theorem popc_eq_card (w X : Nat) :
    popc w X = ((Finset.range w).filter fun j => X.testBit j = true).card := by
  rw [Finset.card_filter]
  unfold popc
  rw [sumN_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Nat.land (Nat.shiftRight X j) 1 = (X >>> j) % 2 := Nat.and_one_is_mod _
  have e2 : X.testBit j = decide ((X >>> j) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [e2]
  rcases Nat.mod_two_eq_zero_or_one (X >>> j) with h | h
  · rw [h]
    exact e.trans h
  · rw [h]
    exact e.trans h

theorem xor_lt {a b : Nat} (ha : a < 128) (hb : b < 128) : a ^^^ b < 128 :=
  Nat.xor_lt_two_pow (n := 7) ha hb

theorem xor_mod (a b : Nat) : (a ^^^ b) % 64 = a % 64 ^^^ b % 64 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have e : (64 : Nat) = 2 ^ 6 := rfl
  simp only [e, Nat.testBit_mod_two_pow, Nat.testBit_xor]
  cases decide (j < 6) <;> simp

theorem add64 : ∀ v < 64, v + 64 = v ^^^ 64 := by decide

theorem land63 (x : Nat) : Nat.land x 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6

theorem act_xor {i a b : Nat} (hi : i < 512) (ha : a < 128) (hb : b < 128) :
    actK i (a ^^^ b) = actK i a ^^^ actK i b := by
  rw [← sA_eq hi (xor_lt ha hb), ← sA_eq hi ha, ← sA_eq hi hb, ← hA hi (xor_lt ha hb), ← hA hi ha,
    ← hA hi hb, CFSG.KC.O8.Mat.matApp_xor]

theorem orbit_mem {u : Nat} (hu : u < 128) (e : Nat) :
    e ∈ p9Orbit u ↔ ∃ i < 512, actK i u = e := by
  unfold p9Orbit
  rw [List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    exact ⟨i, hi, (sA_eq hi hu).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, List.mem_range.2 hi, sA_eq hi hu⟩

theorem orbit_len {u : Nat} (hu : u < 128) :
    (p9Orbit u).length = popc 128 (orN 512 fun i => pw2 (actK i u)) := by
  have hnd : (p9Orbit u).Nodup := List.nodup_dedup _
  refine (List.toFinset_card_of_nodup hnd).symm.trans ?_
  rw [popc_eq_card]
  refine congrArg Finset.card ?_
  ext e
  rw [List.mem_toFinset, orbit_mem hu, Finset.mem_filter, Finset.mem_range, testBit_orN]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨actK_lt _ _, i, hi, rfl⟩
  · rintro ⟨-, h⟩
    exact h

section Sound

variable {ε : Eps} {w Q t : Nat}

structure Hyp (ε : Eps) (w Q t : Nat) : Prop where
  hK : ∀ x < 128, kapCode ε x = kcK w x
  hI : ∀ e < 128, kapInv ε e = kiK w e
  hQ : ∀ v < 64, qfB ε v = bit Q v
  ht : tCode ε = t
  kA : ∀ x < 128, kapAt w x = true
  kB : ∀ i < 512, ∀ v < 64, phiAt actK ginvK w Q i v = true
  kC : ∀ i < 512, ∀ x < 128, actAt actK w i x = true
  kD : ∀ i < 512, movAt actK i = true
  kE : ∀ v < 64, orbAt actK w Q t v = true

variable (H : Hyp ε w Q t)
include H

theorem kapA {x : Nat} (hx : x < 128) :
    kcK w x < 128 ∧ kiK w (kcK w x) = x ∧ kiK w x < 128 ∧ kcK w (kiK w x) = x ∧
      ∀ y < 128, kcK w (x ^^^ y) = kcK w x ^^^ kcK w y := by
  have h := H.kA x hx
  unfold kapAt at h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, allN_true] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun y hy => h.2.2.2.2 y hy⟩

theorem ki_xor {a b : Nat} (ha : a < 128) (hb : b < 128) :
    kiK w (a ^^^ b) = kiK w a ^^^ kiK w b := by
  obtain ⟨-, -, ha1, ha2, -⟩ := kapA H ha
  obtain ⟨-, -, hb1, hb2, -⟩ := kapA H hb
  have e := (kapA H ha1).2.2.2.2 _ hb1
  rw [ha2, hb2] at e
  rw [← e, (kapA H (xor_lt ha1 hb1)).2.1]

theorem phiCode_eq {i v : Nat} (hi : i < 512) (hv : v < 64) :
    phiCode ε i v = phiK actK w i v ∧
      phiK actK w i v = (kiK w (actK i (kcK w v)) ^^^ kiK w (actK i (kcK w 64))) % 64 := by
  have h64 : v + 64 < 128 := by omega
  have hk := (kapA H h64).1
  have hac := actK_lt i (kcK w (v + 64))
  refine ⟨?_, ?_⟩
  · unfold phiCode phiK
    rw [H.hK _ h64, sA_eq hi hk, H.hI _ hac, land63, Nat.add_eq]
  · unfold phiK
    rw [land63, Nat.add_eq, add64 v hv, (kapA H (by omega : v < 128)).2.2.2.2 64 (by decide),
      act_xor hi (kapA H (by omega : v < 128)).1 (kapA H (by decide : (64 : Nat) < 128)).1,
      ki_xor H (actK_lt _ _) (actK_lt _ _)]

theorem L_zero {i : Nat} (hi : i < 512) : kiK w (actK i (kcK w 0)) = 0 := by
  have z : ∀ {a b : Nat}, a = b ^^^ b → a = 0 := fun h => by rw [h, Nat.xor_self]
  have e0 : kcK w 0 = 0 := z (by
    have := (kapA H (by decide : (0 : Nat) < 128)).2.2.2.2 0 (by decide)
    rwa [Nat.zero_xor] at this)
  have e1 : actK i 0 = 0 := z (by
    have := act_xor hi (by decide : (0 : Nat) < 128) (by decide : (0 : Nat) < 128)
    rwa [Nat.zero_xor] at this)
  have e2 : kiK w 0 = 0 := z (by
    have := ki_xor H (by decide : (0 : Nat) < 128) (by decide : (0 : Nat) < 128)
    rwa [Nat.zero_xor] at this)
  rw [e0, e1, e2]

theorem phi_affine {i v u : Nat} (hi : i < 512) (hv : v < 64) (hu : u < 64) :
    phiCode ε i (v ^^^ u) = phiCode ε i v ^^^ phiCode ε i u ^^^ phiCode ε i 0 := by
  have hvu : v ^^^ u < 64 := Nat.xor_lt_two_pow (n := 6) hv hu
  obtain ⟨a1, a2⟩ := phiCode_eq H hi hvu
  obtain ⟨b1, b2⟩ := phiCode_eq H hi hv
  obtain ⟨c1, c2⟩ := phiCode_eq H hi hu
  obtain ⟨d1, d2⟩ := phiCode_eq H hi (by decide : (0 : Nat) < 64)
  rw [a1, a2, b1, b2, c1, c2, d1, d2, L_zero H hi,
    (kapA H (by omega : v < 128)).2.2.2.2 u (by omega),
    act_xor hi (kapA H (by omega : v < 128)).1 (kapA H (by omega : u < 128)).1,
    ki_xor H (actK_lt _ _) (actK_lt _ _)]
  simp only [xor_mod, Nat.zero_xor]
  generalize kiK w (actK i (kcK w v)) % 64 = A
  generalize kiK w (actK i (kcK w u)) % 64 = B
  generalize kiK w (actK i (kcK w 64)) % 64 = C
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor]
  cases A.testBit j <;> cases B.testBit j <;> cases C.testBit j <;> rfl

theorem phi_lt {i v : Nat} (hi : i < 512) (hv : v < 64) : phiCode ε i v < 64 := by
  rw [(phiCode_eq H hi hv).1]
  unfold phiK
  rw [land63]
  exact Nat.mod_lt _ (by decide)

theorem c1 : ((List.range 128).all fun x => decide (kapCode ε x < 128) &&
    kapInv ε (kapCode ε x) == x && decide (kapInv ε x < 128) && kapCode ε (kapInv ε x) == x &&
    (List.range 128).all fun y => kapCode ε (x ^^^ y) == (kapCode ε x ^^^ kapCode ε y)) = true := by
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  intro x hx
  obtain ⟨a1, a2, a3, a4, a5⟩ := kapA H hx
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, fun y hy => ?_⟩
  · rw [H.hK x hx]
    exact a1
  · rw [H.hK x hx, H.hI _ a1, a2]
  · rw [H.hI x hx]
    exact a3
  · rw [H.hI x hx, H.hK _ a3, a4]
  · rw [H.hK _ (xor_lt hx hy), H.hK x hx, H.hK y hy, a5 y hy]

theorem c2 : ((List.range 512).all fun i => (List.range 64).all fun v =>
    decide (phiCode ε i v < 64) && qfB ε (phiCode ε i v) == qfB ε v &&
    phiCode ε (sGinv[i]!) (phiCode ε i v) == v && phiCode ε i (phiCode ε (sGinv[i]!) v) == v &&
    (List.range 64).all fun u =>
      phiCode ε i (v ^^^ u) == (phiCode ε i v ^^^ phiCode ε i u ^^^ phiCode ε i 0)) = true := by
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  intro i hi v hv
  have hb := H.kB i hi v hv
  unfold phiAt at hb
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at hb
  obtain ⟨b1, b2, b3⟩ := hb
  have hg := ginvK_lt i
  have hp := phi_lt H hi hv
  have e1 := (phiCode_eq H hi hv).1
  have hp' : phiK actK w i v < 64 := e1 ▸ hp
  have hq : phiCode ε (ginvK i) v < 64 := phi_lt H hg hv
  have e2 := (phiCode_eq H hg hv).1
  have hq' : phiK actK w (ginvK i) v < 64 := e2 ▸ hq
  rw [sGinv_eq hi]
  refine ⟨⟨⟨⟨hp, ?_⟩, ?_⟩, ?_⟩, fun u hu => phi_affine H hi hv hu⟩
  · rw [H.hQ _ hp, H.hQ v hv, e1]
    unfold beqB at b1
    cases h1 : bit Q (phiK actK w i v) <;> cases h2 : bit Q v <;> simp_all [notB]
  · rw [e1, (phiCode_eq H hg hp').1]
    exact b2
  · rw [e2, (phiCode_eq H hi hq').1]
    exact b3

theorem c3 : ((List.range 512).all fun i => (List.range 128).all fun x =>
    kapInv ε (sA i (kapCode ε x)) == actPhi ε i x) = true := by
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi x hx
  have hc := H.kC i hi x hx
  unfold actAt at hc
  have hk := (kapA H hx).1
  rw [H.hK x hx, sA_eq hi hk, H.hI _ (actK_lt _ _), Nat.eq_of_beq_eq_true hc]
  unfold actPhiK actPhi
  have hm : x % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [bit_eq, land63, ← (phiCode_eq H hi hm).1, ← (phiCode_eq H hi (by decide : (0 : Nat) < 64)).1]
  cases x.testBit 6 <;> rfl

theorem c4 : ((List.range 512).all fun i => i == 0 || (List.range 128).any fun e => sA i e != e) =
    true := by
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
    bne_iff_ne, ne_eq]
  intro i hi
  have hd := H.kD i hi
  unfold movAt at hd
  rw [orB_eq, Bool.or_eq_true, Nat.beq_eq, anyN_true] at hd
  rcases hd with hd | ⟨e, he, hne⟩
  · exact Or.inl hd
  · refine Or.inr ⟨e, he, ?_⟩
    rw [sA_eq hi he]
    rw [notB_eq, Bool.not_eq_true'] at hne
    exact Nat.ne_of_beq_eq_false hne

theorem c5 : ((List.range 64).all fun v => qfB ε v ||
    ((p9Orbit (kapCode ε (v + 64))).length != 4 ||
      (p9Orbit (kapCode ε (v + 64))).contains (tCode ε))) = true := by
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true]
  intro v hv
  have he := H.kE v hv
  unfold orbAt orbMask at he
  have h64 : v + 64 < 128 := by omega
  have hk := (kapA H h64).1
  rw [H.hQ v hv, H.hK _ h64, H.ht]
  rw [orB_eq, orB_eq, Bool.or_eq_true, Bool.or_eq_true, notB_eq] at he
  rcases he with he | he | he
  · exact Or.inl he
  · refine Or.inr (Or.inl ?_)
    rw [orbit_len hk, bne_iff_ne]
    have he' : Nat.beq (popc 128 (orN 512 fun i => pw2 (actK i (kcK w (v + 64))))) 4 = false := by
      rw [Bool.not_eq_true'] at he
      exact he
    exact Nat.ne_of_beq_eq_false he'
  · refine Or.inr (Or.inr ?_)
    rw [List.contains_iff_mem, orbit_mem hk, ← testBit_orN]
    rw [bit_eq] at he
    exact he

theorem dict_sound : dictCheck ε = true := by
  unfold dictCheck
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨⟨c1 H, c2 H⟩, c3 H⟩, c4 H⟩, c5 H⟩

end Sound

end CertificateChecks.KernelO8.Dict

end
