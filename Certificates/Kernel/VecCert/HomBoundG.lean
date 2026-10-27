module

public import Certificates.Kernel.Sporadic.RelSeg
public import CFSG.Sporadic.Bridge.Common

public section

namespace CertificateChecks.KernelHomG

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.RelSeg CFSG.Sporadic.Bridge

variable {d : Nat} {K : Type} [CommRing K]

structure LayoutSound (Q : Nat → Prop) (Mt : Nat → Matrix (Fin d) (Fin d) K)
    (mul : Nat → Nat → Nat) (vld : Nat → Bool) (ONE : Nat) : Prop where
  mul_sound : ∀ A B, Q A → Q B → Q (mul A B) ∧ Mt (mul A B) = Mt A * Mt B
  one_q : Q ONE
  one_mt : Mt ONE = 1
  vld_q : ∀ X, vld X = true → Q X

@[expose] def rootSetG (Mt : Nat → Matrix (Fin d) (Fin d) K) (Lg : Nat) (RB : Nat → Nat) :
    Set (Matrix (Fin d) (Fin d) K) :=
  {M | ∃ g, 0 < g ∧ g ≤ 2 * Lg ∧ M = Mt (RB g)}

@[expose] def RegsInG (Q : Nat → Prop) (Mt : Nat → Matrix (Fin d) (Fin d) K) (Lg : Nat)
    (RB : Nat → Nat) (s : Nat) : Prop :=
  ∀ r, 0 < r → r < s → Q (RB r) ∧ Mt (RB r) ∈ Submonoid.closure (rootSetG Mt Lg RB)

theorem strictN_eqG (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem brec_presG {Q : Nat → Prop} {x y : Nat} (c : Bool) (hx : Q x) (hy : Q y) :
    Q (Bool.rec (motive := fun _ => Nat) x y c) := by
  cases c
  · exact hx
  · exact hy

theorem nrec_presG {Q : Nat → Prop} {x : Nat} {s : Nat → Nat → Nat} (hx : Q x)
    (hs : ∀ i a, Q a → Q (s i a)) : ∀ m, Q (Nat.rec (motive := fun _ => Nat) x s m)
  | 0 => hx
  | m + 1 => hs m _ (nrec_presG hx hs m)

theorem powR_presG {Q : Nat → Prop} {mul : Nat → Nat → Nat} {ONE M : Nat} (e : Nat)
    (hmul : ∀ A B, Q A → Q B → Q (mul A B)) (hone : Q ONE) (hM : Q M) :
    Q (powR mul ONE M e) := by
  unfold powR
  generalize (nat_lit 16) = m
  apply nrec_presG hone
  intro i a ha
  rw [strictN_eqG]
  have hsq := brec_presG (Q := Q) (Nat.beq a ONE) (hmul a a ha ha) ha
  exact brec_presG _ hsq (brec_presG _ (hmul _ _ hsq hM) hM)

theorem inv_mem_of_finiteG {M : Type*} [Monoid M] [Finite M] {C : Submonoid M} {x y : M}
    (hx : x ∈ C) (hxy : x * y = 1) (hyx : y * x = 1) : y ∈ C := by
  let u : Mˣ := ⟨x, y, hxy, hyx⟩
  have : Finite Mˣ := Finite.of_injective (fun v : Mˣ => (v : M)) Units.val_injective
  have hpos := (isOfFinOrder_of_finite u).orderOf_pos
  have e : u⁻¹ = u ^ (orderOf u - 1) := by
    calc u⁻¹ = u⁻¹ * u ^ orderOf u := by rw [pow_orderOf_eq_one, mul_one]
      _ = u⁻¹ * (u * u ^ (orderOf u - 1)) := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      _ = u ^ (orderOf u - 1) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hy : y = ((u ^ (orderOf u - 1) : Mˣ) : M) := by rw [← e]; rfl
  rw [hy, Units.val_pow_eq_pow_val]
  exact pow_mem hx _

theorem rec_andG {f : Nat → Bool} : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m = true →
      ∀ g < m, f g = true
  | 0, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | m + 1, h, g, hg => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m)
        (f m) = true := h
    obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact rec_andG m h1 g hg
    · exact h2

theorem lenL_eqG {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenL l) = _
    rw [lenL_eqG l]
    rfl

theorem nthRel_eqG : ∀ (l : List (List (Nat × Bool))) (k : Nat) (hk : k < l.length),
    nthRel l k = l[k]
  | [], k, hk => absurd hk (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: l, k + 1, hk => by
    change nthRel l k = _
    rw [nthRel_eqG l k (by simp at hk; omega)]
    rfl

@[expose] noncomputable def chunkRunG (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih2 J S => CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (andB (Nat.blt (nat_lit 0) S) (insOK RB mul vld ONE S (bitsN J (nat_lit 0) (nat_lit 50)))))
      (ih2 (Nat.shiftRight J (nat_lit 50))))

theorem chunkRunG_succ (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE m J S : Nat) :
    chunkRunG RB mul vld ONE (m + 1) J S =
      CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
          (andB (Nat.blt (nat_lit 0) S) (insOK RB mul vld ONE S (bitsN J (nat_lit 0) (nat_lit 50)))))
        (chunkRunG RB mul vld ONE m (Nat.shiftRight J (nat_lit 50))) :=
  rfl

theorem runSlp_consG (RB : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool)
    (ONE C : Nat) (Cs : List Nat) (s : Nat) :
    runSlp RB mul vld ONE (C :: Cs) s =
      runSlp RB mul vld ONE Cs (chunkRunG RB mul vld ONE (Nat.land C (nat_lit 255))
        (Nat.shiftRight C (nat_lit 8)) s) :=
  strictN_eqG _ _

variable {Q : Nat → Prop} {Mt : Nat → Matrix (Fin d) (Fin d) K} {mul : Nat → Nat → Nat}
  {vld : Nat → Bool} {ONE : Nat}

theorem slpSeg_soundG [Finite K] {Lg S0 S1 : Nat} {RB : Nat → Nat} {Cs : List Nat}
    (hs : LayoutSound Q Mt mul vld ONE)
    (hS : Nat.beq (runSlp RB mul vld ONE Cs S0) S1 = true)
    (h0 : RegsInG Q Mt Lg RB S0) : RegsInG Q Mt Lg RB S1 := by
  set C := Submonoid.closure (rootSetG Mt Lg RB) with hC
  have : Finite (Matrix (Fin d) (Fin d) K) := inferInstanceAs (Finite (Fin d → Fin d → K))
  let P : Nat → Prop := fun X => Q X ∧ Mt X ∈ C
  have hmulP : ∀ A B, P A → P B → P (mul A B) := by
    intro A B hA hB
    obtain ⟨h1, h2⟩ := hs.mul_sound A B hA.1 hB.1
    exact ⟨h1, by rw [h2]; exact C.mul_mem hA.2 hB.2⟩
  have hP : ∀ r, 0 < r → ∀ s, RegsInG Q Mt Lg RB s → r < s → P (RB r) :=
    fun r hr s hs' hrs => hs' r hr hrs
  have hins : ∀ s ins, RegsInG Q Mt Lg RB s → 0 < s →
      insOK RB mul vld ONE s ins = true → RegsInG Q Mt Lg RB (s + 1) := by
    intro s ins hs' hs0 h
    have hnew : P (RB s) := by
      unfold insOK at h
      generalize Nat.land ins (nat_lit 3) = k at h
      generalize bitsN ins (nat_lit 2) (nat_lit 16) = a at h
      generalize bitsN ins (nat_lit 18) (nat_lit 16) = b at h
      generalize bitsN ins (nat_lit 34) (nat_lit 16) = e at h
      dsimp only at h
      revert h
      cases Nat.beq k (nat_lit 0)
      · cases Nat.beq k (nat_lit 1)
        · cases Nat.beq k (nat_lit 2)
          · intro h
            exact absurd h Bool.false_ne_true
          · intro h
            obtain ⟨ha, h⟩ := (andB_iff _ _).1 h
            obtain ⟨hv, h⟩ := (andB_iff _ _).1 h
            obtain ⟨ha0, has⟩ := (andB_iff _ _).1 ha
            have hPa := hP a (Nat.blt_eq.mp ha0) s hs' (Nat.blt_eq.mp has)
            have hq := hs.vld_q _ hv
            have hm := (hs.mul_sound _ _ hPa.1 hq).2
            rw [Nat.eq_of_beq_eq_true h, hs.one_mt] at hm
            have hxy : Mt (RB a) * Mt (RB s) = 1 := hm.symm
            exact ⟨hq, inv_mem_of_finiteG hPa.2 hxy (mul_eq_one_comm.1 hxy)⟩
        · intro h
          obtain ⟨ha, h⟩ := (andB_iff _ _).1 h
          obtain ⟨-, h⟩ := (andB_iff _ _).1 h
          obtain ⟨ha0, has⟩ := (andB_iff _ _).1 ha
          have hPa := hP a (Nat.blt_eq.mp ha0) s hs' (Nat.blt_eq.mp has)
          have hp := powR_presG (Q := P) e hmulP ⟨hs.one_q, by rw [hs.one_mt]; exact C.one_mem⟩ hPa
          rw [← Nat.eq_of_beq_eq_true h] at hp
          exact hp
      · intro h
        obtain ⟨ha, h⟩ := (andB_iff _ _).1 h
        obtain ⟨hb, h⟩ := (andB_iff _ _).1 h
        obtain ⟨ha0, has⟩ := (andB_iff _ _).1 ha
        obtain ⟨hb0, hbs⟩ := (andB_iff _ _).1 hb
        have hPa := hP a (Nat.blt_eq.mp ha0) s hs' (Nat.blt_eq.mp has)
        have hPb := hP b (Nat.blt_eq.mp hb0) s hs' (Nat.blt_eq.mp hbs)
        have hp := hmulP _ _ hPa hPb
        rw [← Nat.eq_of_beq_eq_true h] at hp
        exact hp
    intro r hr hrs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hrs with hrs | rfl
    · exact hs' r hr hrs
    · exact hnew
  have hzero : RegsInG Q Mt Lg RB 0 := fun r _ hr => absurd hr (Nat.not_lt_zero r)
  have hchunk : ∀ m J s, RegsInG Q Mt Lg RB s →
      RegsInG Q Mt Lg RB (chunkRunG RB mul vld ONE m J s) := by
    intro m
    induction m with
    | zero => intro J s hs'; exact hs'
    | succ m ih =>
      intro J s hs'
      rw [chunkRunG_succ, strictN_eqG]
      refine ih (Nat.shiftRight J (nat_lit 50)) _ ?_
      cases hb : andB (Nat.blt (nat_lit 0) s)
          (insOK RB mul vld ONE s (bitsN J (nat_lit 0) (nat_lit 50)))
      · exact hzero
      · obtain ⟨h1, h2⟩ := (andB_iff _ _).1 hb
        exact hins s _ hs' (Nat.blt_eq.mp h1) h2
  have hrun : ∀ (Cs : List Nat) s, RegsInG Q Mt Lg RB s →
      RegsInG Q Mt Lg RB (runSlp RB mul vld ONE Cs s) := by
    intro Cs
    induction Cs with
    | nil => intro s hs'; exact hs'
    | cons C Cs ih =>
      intro s hs'
      rw [runSlp_consG]
      exact ih _ (hchunk _ _ _ hs')
  rw [← Nat.eq_of_beq_eq_true hS]
  exact hrun Cs S0 h0

theorem regsIn_rootsG {Lg : Nat} {RB : Nat → Nat} (hs : LayoutSound Q Mt mul vld ONE)
    (hroot : rootsOK RB vld 1 (Lg + 1) = true) : RegsInG Q Mt Lg RB (Lg + 1) := by
  intro r hr0 hr
  refine ⟨?_, Submonoid.subset_closure ⟨r, hr0, by omega, rfl⟩⟩
  have h := rec_andG (f := fun i => Bool.rec (motive := fun _ => Bool) true (vld (RB i))
    (Nat.ble 1 i)) (Lg + 1) hroot r hr
  have hb1 : Nat.ble 1 r = true := Nat.ble_eq.mpr hr0
  rw [hb1] at h
  exact hs.vld_q _ h

theorem letM_q {Lg : Nat} {RB : Nat → Nat} (hs : LayoutSound Q Mt mul vld ONE)
    (hroot : rootsOK RB vld 1 (Lg + 1) = true) (hinv : invsOK RB mul vld Lg ONE = true)
    {x : Nat × Bool} (hx : x.1 < Lg) : Q (letM RB Lg x) := by
  obtain ⟨g, s⟩ := x
  cases s
  · have h := rec_andG (f := fun g => andB (vld (RB (Nat.add (Nat.succ Lg) g)))
      (Nat.beq (mul (RB (Nat.succ g)) (RB (Nat.add (Nat.succ Lg) g))) ONE)) Lg hinv g hx
    exact hs.vld_q _ ((andB_iff _ _).1 h).1
  · have h := rec_andG (f := fun i => Bool.rec (motive := fun _ => Bool) true
      (vld (RB i)) (Nat.ble 1 i)) (Lg + 1) hroot (g + 1) (by simp at hx; omega)
    have hb1 : Nat.ble 1 (g + 1) = true := Nat.ble_eq.mpr (by omega)
    rw [hb1] at h
    exact hs.vld_q _ h

theorem pair_of_invsG {Lg : Nat} {RB : Nat → Nat} (hs : LayoutSound Q Mt mul vld ONE)
    (hroot : rootsOK RB vld 1 (Lg + 1) = true) (hinv : invsOK RB mul vld Lg ONE = true) :
    ∀ g < Lg, Mt (RB (g + 1)) * Mt (RB (Lg + 1 + g)) = 1 := by
  intro g hg
  have h := rec_andG (f := fun g => andB (vld (RB (Nat.add (Nat.succ Lg) g)))
    (Nat.beq (mul (RB (Nat.succ g)) (RB (Nat.add (Nat.succ Lg) g))) ONE)) Lg hinv g hg
  obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h
  have hr : Q (RB (g + 1)) := letM_q hs hroot hinv (x := (g, true)) hg
  have h1' : vld (RB (Lg + 1 + g)) = true := h1
  have h2' : mul (RB (g + 1)) (RB (Lg + 1 + g)) = ONE := Nat.eq_of_beq_eq_true h2
  have e := (hs.mul_sound (RB (g + 1)) (RB (Lg + 1 + g)) hr (hs.vld_q _ h1')).2
  rw [← e, h2', hs.one_mt]

variable (Q Mt) in
@[expose] def SegG (Lg : Nat) (RB : Nat → Nat) (rels : List (List (Nat × Bool)))
    (r lo hi Sin Sout : Nat) : Prop :=
  lo ≤ hi ∧ (Q Sin → Q Sout ∧ Mt Sout =
    Mt Sin * ((sel lo hi 0 (nthRel rels r)).map fun x => Mt (letM RB Lg x)).prod)

theorem segG_join {Lg : Nat} {RB : Nat → Nat} {rels : List (List (Nat × Bool))}
    {r a b c S1 S2 S3 : Nat} (h1 : SegG Q Mt Lg RB rels r a b S1 S2)
    (h2 : SegG Q Mt Lg RB rels r b c S2 S3) : SegG Q Mt Lg RB rels r a c S1 S3 := by
  refine ⟨h1.1.trans h2.1, fun hS => ?_⟩
  obtain ⟨hc2, e2⟩ := h1.2 hS
  obtain ⟨hc3, e3⟩ := h2.2 hc2
  refine ⟨hc3, ?_⟩
  rw [e3, e2, mul_assoc, ← List.prod_append, ← List.map_append, sel_append h1.1 h2.1]

theorem nthRel_memG : ∀ (l : List (List (Nat × Bool))) (k : Nat), k < lenL l → nthRel l k ∈ l
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: l, k + 1, hk => by
    change nthRel l k ∈ _
    exact List.mem_cons_of_mem _ (nthRel_memG l k (Nat.lt_of_succ_lt_succ hk))

theorem segG_of_check {Lg r lo hi Sin Sout : Nat} {RB : Nat → Nat}
    {rels : List (List (Nat × Bool))} (hs : LayoutSound Q Mt mul vld ONE)
    (hroot : rootsOK RB vld 1 (Lg + 1) = true) (hinv : invsOK RB mul vld Lg ONE = true)
    (hb : relsBounded rels Lg = true)
    (h : relSegOK RB mul rels ONE Lg r lo hi Sin Sout = true) :
    SegG Q Mt Lg RB rels r lo hi Sin Sout := by
  have h' : andB (Nat.blt r (lenL rels)) (andB (Nat.blt lo hi) (andB (Nat.ble hi (lenL (nthRel rels r)))
      (Nat.beq (segProd RB mul ONE Lg lo hi (nthRel rels r) 0 Sin) Sout))) = true := h
  obtain ⟨hr, h'⟩ := (andB_iff _ _).1 h'
  obtain ⟨hlh, h'⟩ := (andB_iff _ _).1 h'
  obtain ⟨-, h'⟩ := (andB_iff _ _).1 h'
  have hseg := Nat.eq_of_beq_eq_true h'
  have hmem := nthRel_memG rels r (Nat.blt_eq.mp hr)
  have hbd := relsBounded_spec hb _ hmem
  refine ⟨Nat.le_of_lt (Nat.blt_eq.mp hlh), fun hS => ?_⟩
  have hsg := segProd_sel (P := Q) (M := Mt) (lo := lo) (hi := hi) hs.mul_sound hs.one_mt
    (nthRel rels r) 0 Sin hS (fun x hx => letM_q hs hroot hinv (hbd x hx))
  rw [hseg] at hsg
  exact hsg

theorem segG_of_relOK {Lg r : Nat} {RB : Nat → Nat} {rels : List (List (Nat × Bool))}
    (hs : LayoutSound Q Mt mul vld ONE)
    (hroot : rootsOK RB vld 1 (Lg + 1) = true) (hinv : invsOK RB mul vld Lg ONE = true)
    (hb : relsBounded rels Lg = true) (h : relOK RB mul rels Lg ONE r = true) :
    SegG Q Mt Lg RB rels r 0 (lenL (nthRel rels r)) ONE ONE :=
  segG_of_check hs hroot hinv hb h

theorem rel_of_segG {Lg r : Nat} {RB : Nat → Nat} {rels : List (List (Nat × Bool))}
    (hs : LayoutSound Q Mt mul vld ONE)
    (h : SegG Q Mt Lg RB rels r 0 (lenL (nthRel rels r)) ONE ONE) :
    ((nthRel rels r).map fun x => Mt (letM RB Lg x)).prod = 1 := by
  obtain ⟨-, e⟩ := h.2 hs.one_q
  rw [hs.one_mt, one_mul, sel_all 0 _ (Nat.le_refl 0) (by rw [lenL_eqG]; omega)] at e
  exact e.symm

@[expose] noncomputable def flipG (x : Nat × Bool) : Nat × Bool :=
  Prod.rec (motive := fun _ => Nat × Bool) (fun g s => (g, notB s)) x

theorem letEq_specG : ∀ x y : Nat × Bool, letEq x y = true → x = y
  | (g, s), (h, t), hxy => by
    have h' : andB (Nat.beq g h) (Bool.rec (motive := fun _ => Bool) (notB t) t s) = true := hxy
    obtain ⟨e1, e2⟩ := (andB_iff _ _).1 h'
    have e := Nat.eq_of_beq_eq_true e1
    subst e
    cases s <;> cases t <;> first | rfl | exact absurd e2 (by decide)

theorem wordEq_specG : ∀ u v : List (Nat × Bool), wordEq u v = true → u = v
  | [], [], _ => rfl
  | [], _ :: _, h => absurd (h : false = true) Bool.false_ne_true
  | _ :: _, [], h => absurd (h : false = true) Bool.false_ne_true
  | x :: xs, y :: ys, h => by
    have h' : andB (letEq x y) (wordEq xs ys) = true := h
    obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h'
    rw [letEq_specG x y h1, wordEq_specG xs ys h2]

theorem invWord_eqG : ∀ u acc : List (Nat × Bool),
    invWord u acc = (u.map flipG).reverse ++ acc
  | [], _ => rfl
  | x :: u, acc => by
    change invWord u (flipG x :: acc) = _
    rw [invWord_eqG u]
    simp

theorem prod_invG {R : Type*} [Monoid R] {f : Nat × Bool → R} :
    ∀ u : List (Nat × Bool), (∀ x ∈ u, f (flipG x) * f x = 1) →
      ((u.map flipG).reverse.map f).prod * (u.map f).prod = 1
  | [], _ => by simp
  | x :: u, h => by
    have ih := prod_invG u (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (by simp)
    simp only [List.map_cons, List.reverse_cons, List.map_append, List.prod_append, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc, ← mul_assoc (f (flipG x)), hx, one_mul, ih]

theorem rels_of_checksG {Lg : Nat} {RB : Nat → Nat} {rels : List (List (Nat × Bool))}
    (hs : LayoutSound Q Mt mul vld ONE)
    (hroot : rootsOK RB vld 1 (Lg + 1) = true) (hinv : invsOK RB mul vld Lg ONE = true)
    (hb : relsBounded rels Lg = true)
    (hr : ∀ r < lenRels rels, SegG Q Mt Lg RB rels r 0 (lenL (nthRel rels r)) ONE ONE ∨
      ∃ s < r, relDupOK rels s r = true) :
    ∀ v ∈ rels, (v.map fun x => Mt (letM RB Lg x)).prod = 1 := by
  have hpair := pair_of_invsG hs hroot hinv
  have hbd := relsBounded_spec hb
  have hflip : ∀ x : Nat × Bool, x.1 < Lg →
      Mt (letM RB Lg (flipG x)) * Mt (letM RB Lg x) = 1 := by
    rintro ⟨g, s⟩ hg
    cases s
    · exact hpair g hg
    · exact mul_eq_one_comm.1 (hpair g hg)
  have hlen : lenRels rels = rels.length := lenL_eqG rels
  have hrel : ∀ r, r < rels.length →
      ((nthRel rels r).map fun x => Mt (letM RB Lg x)).prod = 1 := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr'
      rcases hr r (by rw [hlen]; exact hr') with h | ⟨s, hs', h⟩
      · exact rel_of_segG hs h
      · have h' : andB (Nat.blt s r) (andB (Nat.blt r (lenL rels))
            (orB (wordEq (nthRel rels r) (nthRel rels s))
              (wordEq (nthRel rels r) (invWord (nthRel rels s) [])))) = true := h
        obtain ⟨-, h'⟩ := (andB_iff _ _).1 h'
        obtain ⟨-, h'⟩ := (andB_iff _ _).1 h'
        have hsl : s < rels.length := by omega
        have hsmem : nthRel rels s ∈ rels := by
          rw [nthRel_eqG rels s hsl]
          exact List.getElem_mem hsl
        have hor : wordEq (nthRel rels r) (nthRel rels s) = true ∨
            wordEq (nthRel rels r) (invWord (nthRel rels s) []) = true := by
          revert h'
          cases wordEq (nthRel rels r) (nthRel rels s)
          · exact Or.inr
          · exact fun _ => Or.inl rfl
        rcases hor with h'' | h''
        · rw [wordEq_specG _ _ h'']
          exact ih s hs' hsl
        · rw [wordEq_specG _ _ h'', invWord_eqG, List.append_nil]
          have hp := prod_invG (f := fun x => Mt (letM RB Lg x)) (nthRel rels s)
            (fun x hx => hflip x (hbd _ hsmem x hx))
          rw [ih s hs' hsl, mul_one] at hp
          exact hp
  intro v hv
  obtain ⟨r, hr', rfl⟩ := List.getElem_of_mem hv
  rw [← nthRel_eqG rels r hr']
  exact hrel r hr'

theorem le_range_of_homG (P : TauCeti.GroupPresentation) {Lg Sfin hA hB : Nat} {RB : Nat → Nat}
    {rels : List (List (Nat × Bool))} {MA MB : Matrix (Fin d) (Fin d) K}
    (hs : LayoutSound Q Mt mul vld ONE)
    (hrelsP : P.relatorLetters = rels) (hgen : P.generatorCount = Lg)
    (hroot : rootsOK RB vld 1 (Lg + 1) = true) (hinv : invsOK RB mul vld Lg ONE = true)
    (hb : relsBounded rels Lg = true)
    (hrel : ∀ v ∈ rels, (v.map fun x => Mt (letM RB Lg x)).prod = 1)
    (hregs : RegsInG Q Mt Lg RB Sfin)
    (hA0 : 0 < hA) (hAS : hA < Sfin) (hB0 : 0 < hB) (hBS : hB < Sfin)
    (hmA : MA = Mt (RB hA)) (hmB : MB = Mt (RB hB)) :
    ∃ φ : P.Group →* GL (Fin d) K,
      ∀ g : GL (Fin d) K, g.val = MA ∨ g.val = MB → g ∈ φ.range := by
  have hX := pair_of_invsG hs hroot hinv
  set X : Nat → Matrix (Fin d) (Fin d) K := fun r => Mt (RB r) with hXdef
  have hXl : ∀ g < Lg, X (Lg + 1 + g) * X (g + 1) = 1 := fun g hg => mul_eq_one_comm.mp (hX g hg)
  let uX : Nat → GL (Fin d) K := fun g =>
    if hg : g < Lg then ⟨X (g + 1), X (Lg + 1 + g), hX g hg, hXl g hg⟩ else 1
  have huX : ∀ g (hg : g < Lg), (uX g : Matrix (Fin d) (Fin d) K) = X (g + 1) := by
    intro g hg
    simp [uX, hg]
  have huXi : ∀ g (hg : g < Lg), ((uX g)⁻¹ : GL (Fin d) K).val = X (Lg + 1 + g) := by
    intro g hg
    simp [uX, hg]
  have hletv : ∀ x : Nat × Bool, x.1 < Lg →
      ((if x.2 then uX x.1 else (uX x.1)⁻¹ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = Mt (letM RB Lg x) := by
    rintro ⟨g, s⟩ hg
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [huXi g hg]
      rfl
    · simp only [↓reduceIte]
      rw [huX g hg]
      rfl
  have hrelP : ∀ v ∈ P.relatorLetters, wordProd uX v = 1 := by
    intro v hv
    rw [hrelsP] at hv
    have hlt := relsBounded_spec hb v hv
    apply Units.ext
    rw [wordProd, Units.val_one, ← hrel v hv, ← Units.coeHom_apply, map_list_prod, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro x hx
    exact hletv x (hlt x hx)
  have hg : ∀ i < Lg, i < P.generatorCount := fun i hi => hgen ▸ hi
  let φ := presHom P uX hrelP
  have hcl : ∀ M ∈ Submonoid.closure (rootSetG Mt Lg RB),
      ∃ u ∈ φ.range, (u : Matrix (Fin d) (Fin d) K) = M := by
    intro M hM
    induction hM using Submonoid.closure_induction with
    | mem M hM =>
      obtain ⟨g, hg0, hg2, rfl⟩ := hM
      rcases Nat.lt_or_ge Lg g with hgl | hgl
      · refine ⟨(uX (g - Lg - 1))⁻¹,
          Subgroup.inv_mem _ ⟨presGen P (g - Lg - 1), presHom_presGen P uX hrelP (hg _ (by omega))⟩, ?_⟩
        rw [huXi _ (by omega)]
        have e : Lg + 1 + (g - Lg - 1) = g := by omega
        rw [e]
      · refine ⟨uX (g - 1), ⟨presGen P (g - 1), presHom_presGen P uX hrelP (hg _ (by omega))⟩, ?_⟩
        rw [huX _ (by omega)]
        have e : g - 1 + 1 = g := by omega
        rw [e]
    | one => exact ⟨1, Subgroup.one_mem _, rfl⟩
    | mul M N _ _ hM hN =>
      obtain ⟨u, hu, rfl⟩ := hM
      obtain ⟨v, hv, rfl⟩ := hN
      exact ⟨u * v, Subgroup.mul_mem _ hu hv, rfl⟩
  have hseed : ∀ (M : Matrix (Fin d) (Fin d) K) (r : Nat), 0 < r → r < Sfin →
      M = Mt (RB r) → ∀ g : GL (Fin d) K, g.val = M → g ∈ φ.range := by
    intro M r hr0 hrS hM g hg
    obtain ⟨u, hu, hval⟩ := hcl _ (hregs r hr0 hrS).2
    have : g = u := Units.ext (by rw [hg, hM, ← hval])
    rw [this]
    exact hu
  refine ⟨φ, fun g hg => ?_⟩
  rcases hg with hg | hg
  · exact hseed MA hA hA0 hAS hmA g hg
  · exact hseed MB hB hB0 hBS hmB g hg

end CertificateChecks.KernelHomG

end
