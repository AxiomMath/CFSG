module

public import Certificates.Kernel.Sporadic.OddCore.Beta24603CK
public import Certificates.Kernel.Sporadic.OddCore.Beta24603L
public import Certificates.Kernel.Sporadic.OddCore.J3BetaA5F
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import CFSG.Certificates.Kernel.Spor.ColHSound
public import CFSG.Certificates.Kernel.Spor.MulHInvSound
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.RuInvHash

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.B24603

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KC.PkPow CFSG.KS.ColH CFSG.KC.MonsterConv.Perm
open CertificateChecks.KernelSpor.J3BetaA5 (hkey_inj_of idxTH_of memTH_of beta_tab)
open CertificateChecks.KernelSporSch

local notation "⟪" x "⟫" => tabT (unpack 6156 13 x)

theorem treeImg_eq (pg : Array Table) (par lab : Array ℕ) (m : ℕ) :
    treeImg pg par lab m = (List.range' 1 (m - 1)).foldl
      (fun r j => r.push (compT 6 r[par[j]!]! pg[lab[j]!]!)) #[idT 6] := by
  unfold treeImg
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.div_one,
    Nat.add_sub_cancel, List.forIn_pure_yield_eq_foldl, bind_pure]
  rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem pows (P : Nat) : Pows 6156 13 P (ppw 6156 13 P) :=
  ⟨rfl, fun e => strictN_eq' (ppw 6156 13 P e) (fun q => pcomp 6156 13 (mask 13) P q)⟩

theorem not_of_bIf {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem divParts3 : CFSG.Sporadic.Schreier.Native.divParts 3 = [1] := by decide

theorem base : szOK 6156 13 = true ∧ J3BetaA5.cK idK = true ∧
    CFSG.KS.Prim.idK 6156 13 (mask 13) = true ∧ J3BetaA5.cK (J3BetaP 7) = true ∧
    J3BetaA5.cK (B24603I 2) = true ∧
    invEqK 6156 13 (mask 13) (6156 * 13) (J3BetaP 7) (B24603I 2) = true ∧
    Nat.beq (J3BetaA5.pc (J3BetaP 7) (J3BetaP 7)) (B24603I 2) = true ∧
    allN 2 (fun j => bAnd(J3BetaA5.cK (J3BetaP (Nat.add j 8)), bAnd(J3BetaA5.cK (B24603I j),
      bAnd(invEqK 6156 13 (mask 13) (6156 * 13) (J3BetaP (Nat.add j 8)) (B24603I j),
      Nat.beq (J3BetaA5.pc (J3BetaP 7) (J3BetaP (Nat.add j 8)))
        (J3BetaA5.pc (J3BetaP (Nat.add j 8)) (J3BetaP 7)))))) = true ∧
    Nat.beq (ppw 6156 13 (J3BetaP 7) 3) idK = true ∧
    bIf(Nat.beq (ppw 6156 13 (J3BetaP 7) 1) idK, false, true) = true ∧
    j3W tWord (J3BetaP 8) = true ∧ j3W dWord (J3BetaP 9) = true ∧ j3W bWord (J3BetaP 7) = true ∧
    Nat.beq (J3BetaP 8) (J3CentP 9) = true := by
  simpa only [bAnd_iff] using base_ok

theorem hidc : canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) = true := base.2.1

theorem hidA : CFSG.Monster.B.Co2.Native.idA 6156 = unpack 6156 13 (pidn 6156 13) := idA_eq base.1

theorem hbc : canonK 6156 13 (mask 13) (6156 * 13) (J3BetaP 7) = true := base.2.2.2.1

theorem hb2c : canonK 6156 13 (mask 13) (6156 * 13) (B24603I 2) = true := base.2.2.2.2.1

theorem hb2 : pcomp 6156 13 (mask 13) (J3BetaP 7) (J3BetaP 7) = B24603I 2 :=
  Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.1

theorem gen {j : ℕ} (hj : j < 2) : J3BetaA5.cK (J3BetaP (j + 8)) = true ∧
    J3BetaA5.cK (B24603I j) = true ∧
    invEqK 6156 13 (mask 13) (6156 * 13) (J3BetaP (j + 8)) (B24603I j) = true ∧
    pcomp 6156 13 (mask 13) (J3BetaP 7) (J3BetaP (j + 8)) =
      pcomp 6156 13 (mask 13) (J3BetaP (j + 8)) (J3BetaP 7) := by
  have h := allN_spec base.2.2.2.2.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2⟩

@[expose] noncomputable def gensK : Array Table := #[⟪J3BetaP 8⟫, ⟪J3BetaP 9⟫]

theorem gens_eq : #[j3BetaTbl 8, j3BetaTbl 9] = gensK := by
  rw [beta_tab (by norm_num), beta_tab (by norm_num)]
  rfl

theorem gensK_size : gensK.size = 2 := rfl

theorem gensK_get {l : ℕ} (hl : l < 2) : gensK[l]! = ⟪J3BetaP (l + 8)⟫ := by
  rw [getElem!_pos gensK l (by rw [gensK_size]; exact hl)]
  interval_cases l <;> simp [gensK]

theorem tab_toNat {X i : ℕ} (hX : canonK 6156 13 (mask 13) (6156 * 13) X = true) (hi : i < 6156) :
    ((⟪X⟫)[i]!).toNat = pg 13 (mask 13) X i := by
  rw [tabT_get, UInt32.toNat_ofNat', CFSG.KC.Misc.PairCount.unpack_get hi,
    Nat.mod_eq_of_lt (by have := pg_lt' hX hi; omega)]

@[expose] noncomputable def genPt(l i : ℕ) : ℕ := pg 13 (mask 13) (J3BetaP (l + 8)) i

theorem x_all : ∀ s < 12, x24603 s = true := by
  intro s hs
  interval_cases s
  exacts [x246030, x246031, x246032, x246033, x246034, x246035, x246036, x246037, x246038,
    x246039, x2460310, x2460311]

theorem hpin : ∀ l < 2, pinK 11 (netL l) (B24603Pi l) = true := by
  intro l hl
  interval_cases l
  exacts [x24603pin0, x24603pin1]

theorem hcol : ∀ l < 2, ∀ i < 6156,
    netApply (11 + 4) (Nat.shiftLeft 1 (11 + 4)) 1 (netL l) (B24603Col (genPt l i)) = B24603Col i := by
  intro l hl i hi
  have h := x_all (6 * l + i / 1026) (by omega)
  unfold x24603 at h
  have e1 : Nat.div (6 * l + i / 1026) 6 = l := by change (6 * l + i / 1026) / 6 = l; omega
  have e2 : Nat.mod (6 * l + i / 1026) 6 = i / 1026 := by
    change (6 * l + i / 1026) % 6 = i / 1026; omega
  rw [e1, e2] at h
  have := colSlK_spec h i (by change 1026 * (i / 1026) ≤ i; omega)
    (by change i < 1026 * (i / 1026) + 1026; omega)
  have e3 : Nat.add 8 l = l + 8 := by change 8 + l = l + 8; omega
  rw [e3] at this
  exact this

theorem hg : ∀ l < 2, ∀ i < 6156, ((gensK[l]!)[i]!).toNat = genPt l i ∧ genPt l i < 6156 := by
  intro l hl i hi
  rw [gensK_get hl]
  exact ⟨tab_toNat (gen hl).1 hi, pg_lt' (gen hl).1 hi⟩

theorem hsort : allN 1080 (hsortK 135 (hashColK 135 6156 B24603Col) 1080 (B24603Hs 0) (B24603Hs 1)) =
    true := by
  rw [Nat.eq_of_beq_eq_true x24603hash]
  exact x24603sort

@[expose] noncomputable def TK (j : ℕ) : Table := colT 6156 B24603Col j

theorem hRep : CFSG.KS.HBfs.HReplay (hkey 6156) (fun j y => compT 6156 y gensK[j]!) gensK.size
    (idT 6156) 1080 TK (lane16 (B24603Tr 0)) (lane16 (B24603Tr 1))
      (fun h l => lane16 (B24603Tr 2) (2 * h + l)) :=
  col_replay (M := 135) (kL := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hpin
    hcol rfl hg x24603idx x24603root hsort

@[expose] noncomputable def LK : Array Table := Array.ofFn (n := 1080) fun i => TK i.val

@[expose] noncomputable def PA : Array ℕ := Array.ofFn (n := 1080) fun i => lane16 (B24603Tr 0) i.val

@[expose] noncomputable def LA : Array ℕ := Array.ofFn (n := 1080) fun i => lane16 (B24603Tr 1) i.val

theorem LK_size : LK.size = 1080 := by simp [LK]

theorem LK_get {i : ℕ} (hi : i < 1080) : LK[i]! = TK i := ofFnH_get _ hi

theorem PA_get {i : ℕ} (hi : i < 1080) : PA[i]! = lane16 (B24603Tr 0) i := ofFnH_get _ hi

theorem LA_get {i : ℕ} (hi : i < 1080) : LA[i]! = lane16 (B24603Tr 1) i := ofFnH_get _ hi

theorem mul_eq : mulClosureH 6156 gensK 1100 = (LK, PA, LA) := by
  have e1 : mulClosureH 6156 gensK 1100 =
      CFSG.KS.HBfs.hbfs (hkey 6156) (fun l y => compT 6156 y gensK[l]!) gensK.size (idT 6156)
        1100 := rfl
  exact e1.trans (CFSG.KS.HBfs.hbfs_replay hRep (by norm_num))

theorem LK_inj : ∀ a < LK.size, ∀ b < LK.size, hkey 6156 LK[a]! = hkey 6156 LK[b]! → a = b := by
  intro a ha b hb e
  rw [LK_size] at ha hb
  rw [LK_get ha, LK_get hb] at e
  exact hRep.kinj a ha b hb e

theorem close {k l : ℕ} (hk : k < 1080) (hl : l < 2) : lane16 (B24603Tr 2) (2 * k + l) < 1080 ∧
    compT 6156 LK[k]! gensK[l]! = LK[lane16 (B24603Tr 2) (2 * k + l)]! := by
  obtain ⟨c1, c2, -⟩ := hRep.close k hk l (by rw [gensK_size]; exact hl)
  refine ⟨c1, ?_⟩
  rw [LK_get hk, LK_get c1]
  exact c2

theorem inv_pt {l : ℕ} (hl : l < 2) {i : ℕ} (hi : i < 6156) :
    pg 13 (mask 13) (B24603I l) i < 6156 ∧ genPt l (pg 13 (mask 13) (B24603I l) i) = i := by
  obtain ⟨g1, g2, g3, -⟩ := gen hl
  obtain ⟨-, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts g3
  have hsurj := surj_of_inj (n := 6156) (f := genPt l) (fun a ha => (h3 a ha).1)
    (fun a ha b hb e => by rw [← (h3 a ha).2, ← (h3 b hb).2]; exact congrArg _ e)
  obtain ⟨a, ha, e⟩ := hsurj i hi
  refine ⟨pg_lt' g2 hi, ?_⟩
  rw [← e]
  unfold genPt
  rw [(h3 a ha).2]

theorem close_inv {k l : ℕ} (hk : k < 1080) (hl : l < 2) : lane16 (B24603Pi l) k < 1080 ∧
    compT 6156 LK[k]! (invT 6156 gensK[l]!) = LK[lane16 (B24603Pi l) k]! := by
  have hp := pi_lt x24603idx hl k hk
  refine ⟨hp, ?_⟩
  obtain ⟨g1, g2, g3, -⟩ := gen hl
  rw [gensK_get hl, invT_unpack (by norm_num) g3, LK_get hk, LK_get hp]
  have := col_inv (n := 6156) (kL := 11) (C := B24603Col) (I := pg 13 (mask 13) (B24603I l))
    (by norm_num) hpin hcol hl (fun i hi => ⟨tab_toNat g2 hi, inv_pt hl hi⟩)
    (q := k) (by omega)
  rw [Nat.mod_eq_of_lt (by omega)] at this
  exact this

@[expose] noncomputable def labT (k : Nat) : Table := tabT (unpack 6 3 (B24603L k))

theorem cay : cayG = true ∧ ∀ k < 1080, cayP k = true := by
  have h := cay24603
  rw [bAnd_iff] at h
  exact ⟨h.1, allN_spec h.2⟩

theorem cayG_spec : B24603L 0 = 181896 ∧ lane16 (B24603Bk 0) 0 < 1080 ∧
    lane16 (B24603Bk 0) 1 < 1080 ∧ ∀ l < 2, canonK 6 3 (mask 3) (6 * 3) (piP l) = true ∧
      invEqK 6 3 (mask 3) (6 * 3) (piP l) (inv6 (piP l)) = true := by
  have h := cay.1
  unfold cayG at h
  simp only [bAnd_iff] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, Nat.blt_eq.mp h.2.1, Nat.blt_eq.mp h.2.2.1, fun l hl => ?_⟩
  have := allN_spec h.2.2.2 l hl
  simp only [bAnd_iff] at this
  exact this

theorem cayP_spec {k : ℕ} (hk : k < 1080) : canonK 6 3 (mask 3) (6 * 3) (B24603L k) = true ∧
    invEqK 6 3 (mask 3) (6 * 3) (B24603L k) (inv6 (B24603L k)) = true ∧
    (k = 0 ∨ B24603L k = pcomp 6 3 (mask 3) (B24603L (lane16 (B24603Tr 0) k))
      (piP (lane16 (B24603Tr 1) k))) ∧
    (∀ l < 2, B24603L (lane16 (B24603Tr 2) (2 * k + l)) = pcomp 6 3 (mask 3) (B24603L k) (piP l)) ∧
    Nat.beq (B24603L k) 181896 = kerI k := by
  have h := cay.2 k hk
  unfold cayP at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, ?_, fun l hl => Nat.eq_of_beq_eq_true (allN_spec h4 l hl), ?_⟩
  · rw [bIf_eq] at h3
    by_cases h0 : Nat.beq k 0 = true
    · exact Or.inl (Nat.eq_of_beq_eq_true h0)
    · rw [if_neg h0] at h3
      exact Or.inr (Nat.eq_of_beq_eq_true h3)
  · rw [bIf_eq, bIf_eq] at h5
    cases e : Nat.beq (B24603L k) 181896 <;> cases f : kerI k <;> simp_all

theorem piP_tab {l : ℕ} (hl : l < 2) : tabT (unpack 6 3 (piP l)) = piGens[l]! := by
  interval_cases l <;> decide +kernel

theorem id6 : idT 6 = tabT (unpack 6 3 181896) := by decide +kernel

theorem id6c : canonK 6 3 (mask 3) (6 * 3) 181896 = true := by decide +kernel

theorem lab_step {k : ℕ} (hk : k < 1080) (h0 : 0 < k) :
    labT k = compT 6 (labT (lane16 (B24603Tr 0) k)) piGens[lane16 (B24603Tr 1) k]! := by
  obtain ⟨t1, t2, -, -⟩ := (idxK_spec (allN_spec x24603idx k hk)).2.1 h0
  rcases (cayP_spec hk).2.2.1 with e | e
  · omega
  · unfold labT
    rw [e, ← piP_tab t2, compT_unpack (cayP_spec (by omega)).1 (cayG_spec.2.2.2 _ t2).1]

theorem lab_close {k l : ℕ} (hk : k < 1080) (hl : l < 2) :
    labT (lane16 (B24603Tr 2) (2 * k + l)) = compT 6 (labT k) piGens[l]! := by
  unfold labT
  rw [(cayP_spec hk).2.2.2.1 l hl, ← piP_tab hl,
    compT_unpack (cayP_spec hk).1 (cayG_spec.2.2.2 l hl).1]

theorem fold_ofFn {pg : Array Table} {par lab : Array ℕ} {L : ℕ → Table} {m : ℕ}
    (h0 : L 0 = idT 6)
    (hs : ∀ k, 1 ≤ k → k < m → par[k]! < k ∧ L k = compT 6 (L par[k]!) pg[lab[k]!]!) :
    ∀ j, j < m → (List.range' 1 j).foldl (fun r k => r.push (compT 6 r[par[k]!]! pg[lab[k]!]!))
      #[idT 6] = Array.ofFn (n := j + 1) fun i => L i.val := by
  intro j
  induction j with
  | zero =>
    intro _
    apply Array.ext (by simp)
    intro i h1 _
    have hi : i = 0 := by simpa using h1
    subst hi
    simp [h0]
  | succ j ih =>
    intro hj
    rw [List.range'_concat, List.foldl_append, ih (by omega), Nat.one_mul]
    simp only [List.foldl_cons, List.foldl_nil]
    obtain ⟨hp, hL⟩ := hs (1 + j) (by omega) (by omega)
    rw [Array.ofFn_succ (n := j + 1)]
    have hg : (Array.ofFn (n := j + 1) fun i => L i.val)[par[1 + j]!]! = L par[1 + j]! := by
      rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
    rw [hg, ← hL, Nat.add_comm 1 j]
    rfl

@[expose] noncomputable def IK : Array Table := Array.ofFn (n := 1080) fun i => labT i.val

theorem IK_get {k : ℕ} (hk : k < 1080) : IK[k]! = labT k := ofFnH_get _ hk

theorem lab0 : labT 0 = idT 6 := by
  unfold labT
  rw [cayG_spec.1, id6]

theorem himg : treeImg piGens PA LA LK.size = IK := by
  rw [treeImg_eq, LK_size]
  have hs : ∀ k, 1 ≤ k → k < 1080 →
      PA[k]! < k ∧ labT k = compT 6 (labT PA[k]!) piGens[LA[k]!]! := by
    intro k hk1 hk
    rw [PA_get hk, LA_get hk]
    exact ⟨((idxK_spec (allN_spec x24603idx k hk)).2.1 (by omega)).1, lab_step hk (by omega)⟩
  exact fold_ofFn (L := labT) (m := 1080) lab0 hs 1079 (by norm_num)

theorem tblEq_hkey {n : ℕ} {x y : Table} (h : tblEq n x y = true) : hkey n x = hkey n y := by
  unfold tblEq at h
  rw [CFSG.KS.TW.allIn_iff] at h
  have hxy : ∀ i < n, x[i]! = y[i]! := fun i hi => by
    have := h i hi
    unfold ap at this
    exact UInt32.toNat_inj.1 (beq_iff_eq.1 this)
  unfold hkey
  have key : ∀ r ≤ n, Nat.fold r (fun i _ h => (h ^^^ (x[i]!).toUInt64) * 1099511628211)
      (14695981039346656037 : UInt64) =
      Nat.fold r (fun i _ h => (h ^^^ (y[i]!).toUInt64) * 1099511628211) 14695981039346656037 := by
    intro r
    induction r with
    | zero =>
      intro _
      rw [Nat.fold_zero, Nat.fold_zero]
    | succ r ih =>
      intro hr
      rw [Nat.fold_succ, Nat.fold_succ, ih (by omega), hxy r (by omega)]
  exact key n (Nat.le_refl n)

theorem TK_eq_iff {a b : ℕ} (ha : a < 1080) (hb : b < 1080) :
    tblEq 6156 (TK a) (TK b) = decide (a = b) := by
  by_cases e : a = b
  · subst e
    rw [tblEqH_self, decide_eq_true rfl]
  · rw [decide_eq_false e]
    cases h : tblEq 6156 (TK a) (TK b)
    · rfl
    · exact absurd (hRep.kinj a ha b hb (tblEq_hkey h)) e

theorem TK_lane {j X : ℕ} (hX : canonK 6156 13 (mask 13) (6156 * 13) X = true)
    (h : laneEqK B24603Col 6156 13 8191 j X = true) : TK j = ⟪X⟫ := by
  apply Array.ext (by rw [TK, colT_size]; simp [tabT, unpack])
  intro i h1 _
  have hi : i < 6156 := by rwa [TK, colT_size] at h1
  rw [← getElem!_pos (TK j) i h1, ← getElem!_pos (⟪X⟫) i (by simp [tabT, unpack]; exact hi), TK,
    colT_get hi, tabT_get, CFSG.KC.Misc.PairCount.unpack_get hi]
  rw [Nat.eq_of_beq_eq_true (allN_spec h i hi)]
  rfl

theorem beta_TK : TK (lane16 (B24603Bk 0) 0) = ⟪J3BetaP 7⟫ ∧ TK (lane16 (B24603Bk 0) 1) = ⟪B24603I 2⟫ := by
  have h := x24603beta
  rw [bAnd_iff] at h
  exact ⟨TK_lane hbc h.1, TK_lane hb2c h.2⟩

theorem ker_eq {k : ℕ} (hk : k < 1080) :
    (tblEq 6156 LK[k]! (idT 6156) || tblEq 6156 LK[k]! (j3BetaTbl 7) ||
      tblEq 6156 LK[k]! (compT 6156 (j3BetaTbl 7) (j3BetaTbl 7))) = kerI k := by
  obtain ⟨-, hk1, hk2, -⟩ := cayG_spec
  rw [LK_get hk, beta_tab (by norm_num), compT_unpack hbc hbc, hb2, ← beta_TK.1, ← beta_TK.2,
    ← colT_root x24603root]
  change (tblEq 6156 (TK k) (TK 0) || _ || _) = _
  rw [TK_eq_iff hk (by norm_num), TK_eq_iff hk hk1, TK_eq_iff hk hk2]
  unfold kerI
  simp only [bIf_eq, Nat.beq_eq, decide_eq_true_eq]
  by_cases e0 : k = 0 <;> by_cases e1 : k = lane16 (B24603Bk 0) 0 <;>
    by_cases e2 : k = lane16 (B24603Bk 0) 1 <;> simp [e0, e1, e2, Nat.beq_eq] <;>
    exact Bool.eq_false_iff.2 fun h => e2 (Nat.eq_of_beq_eq_true h)

theorem facts24603a : j3BetaOK = true := by
  obtain ⟨-, -, -, -, -, hIb, -, -, ho3, ho1, -⟩ := base
  unfold j3BetaOK betaHomCheck
  dsimp only
  rw [gens_eq, mul_eq]
  dsimp only
  rw [himg]
  simp only [Bool.and_eq_true]
  have g0 := gen (j := 0) (by norm_num)
  have g1 := gen (j := 1) (by norm_num)
  have ho1' : Nat.beq (ppw 6156 13 (J3BetaP 7) 1) idK = false := by
    cases h : Nat.beq (ppw 6156 13 (J3BetaP 7) 1) idK
    · rfl
    · rw [h] at ho1
      exact absurd ho1 (by decide)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← Array.all_toList]
    simp only [gensK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact permOK_unpack g0.1 g0.2.2.1
    · rw [invT_unpack (by norm_num) g0.2.2.1]
      exact invOK_unpack g0.1 g0.2.1 g0.2.2.1
    · exact permOK_unpack g1.1 g1.2.2.1
    · rw [invT_unpack (by norm_num) g1.2.2.1]
      exact invOK_unpack g1.1 g1.2.1 g1.2.2.1
  · rw [beta_tab (by norm_num)]
    exact permOK_unpack hbc hIb
  · rw [← Array.all_toList, List.all_eq_true]
    intro x hx
    have : x ∈ [piGens[0]!, piGens[1]!] := by simpa [piGens] using hx
    rcases List.mem_pair.1 this with rfl | rfl
    · rw [← piP_tab (by norm_num)]
      exact permOK_unpack (cayG_spec.2.2.2 0 (by norm_num)).1 (cayG_spec.2.2.2 0 (by norm_num)).2
    · rw [← piP_tab (by norm_num)]
      exact permOK_unpack (cayG_spec.2.2.2 1 (by norm_num)).1 (cayG_spec.2.2.2 1 (by norm_num)).2
  · rw [beta_tab (by norm_num), ordTest_unpack (pows _) hidA hidc hbc, divParts3]
    have ho3' : Nat.beq (ppw 6156 13 (J3BetaP 7) 3) (pidn 6156 13) = true := ho3
    have ho1'' : Nat.beq (ppw 6156 13 (J3BetaP 7) 1) (pidn 6156 13) = false := ho1'
    simp only [List.all_cons, List.all_nil, ho3', ho1'', Bool.not_false, Bool.and_true]
  · rw [← Array.all_toList, beta_tab (by norm_num)]
    simp only [gensK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [commTT_unpack hbc g0.1, g0.2.2.2]
      exact Nat.beq_refl _
    · rw [commTT_unpack hbc g1.1, g1.2.2.2]
      exact Nat.beq_refl _
  · exact mulTree_of hRep
  · exact hkeysDistinct_ofFn fun a ha b hb e => hRep.kinj a ha b hb (UInt64.toNat_inj.1 e)
  · unfold closedOKH
    rw [Array.all_eq_true]
    intro i hi
    rw [Array.all_eq_true]
    intro l hl
    have hi' : i < 1080 := by rw [← LK_size]; exact hi
    have hl' : l < 4 := by simpa [gensK] using hl
    rw [← getElem!_pos LK i hi, ← getElem!_pos _ l hl]
    by_cases h2 : l < 2
    · have hg : (gensK ++ gensK.map (invT 6156))[l]! = gensK[l]! := by
        rw [getElem!_pos _ l (by simp [gensK]; omega), getElem!_pos gensK l (by simp [gensK]; omega),
          Array.getElem_append_left]
      obtain ⟨hq, he⟩ := close hi' h2
      rw [hg, he]
      exact memTH_of LK_inj (by rw [LK_size]; exact hq) (tblEqH_self _ _)
    · have hg : (gensK ++ gensK.map (invT 6156))[l]! = invT 6156 gensK[l - 2]! := by
        rw [getElem!_pos _ l (by simp [gensK]; omega), getElem!_pos gensK (l - 2) (by simp [gensK]; omega),
          Array.getElem_append_right (by simp [gensK]; omega)]
        obtain e | e : l - 2 = 0 ∨ l - 2 = 1 := by omega
        · simp [gensK, e]
        · simp [gensK, e]
      obtain ⟨hq, he⟩ := close_inv hi' (l := l - 2) (by omega)
      rw [hg, he]
      exact memTH_of LK_inj (by rw [LK_size]; exact hq) (tblEqH_self _ _)
  · rw [LK_size]
    rfl
  · simp [IK, LK_size]
  · rw [Array.all_eq_true]
    intro k hk
    have hk' : k < 1080 := by simpa [IK] using hk
    rw [← getElem!_pos IK k hk, IK_get hk']
    exact permOK_unpack (cayP_spec hk').1 (cayP_spec hk').2.1
  · rw [IK_get (by norm_num), lab0]
    exact tblEqH_self _ _
  · rw [LK_size, List.all_eq_true]
    intro k hk
    rw [List.all_eq_true]
    intro l hl
    have hk' := List.mem_range.1 hk
    have hl' := List.mem_range.1 hl
    obtain ⟨hq, he⟩ := close hk' hl'
    rw [he, idxTH_of LK_inj (by rw [LK_size]; exact hq) (tblEqH_self _ _)]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hq, ?_⟩
    rw [IK_get hq, IK_get hk', lab_close hk' hl']
    exact tblEqH_self _ _
  · rw [LK_size, List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    rw [ker_eq hk', IK_get hk', ← (cayP_spec hk').2.2.2.2]
    unfold labT
    rw [id6, tblEq_unpack (cayP_spec hk').1 id6c]
    exact beq_self_eq_true _

theorem cent_eq {k : Nat} (hk : k < 31) : j3CentTbl k = ⟪J3CentP k⟫ := by
  rw [← OddCore.j3CentTbl_eq hk, tabT_natArr]

theorem facts24603b : j3MemOK = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ht, hd, hb, hc⟩ := base
  have c8 : canonK 6156 13 (mask 13) (6156 * 13) (J3BetaP 8) := (gen (j := 0) (by norm_num)).1
  have c9 : canonK 6156 13 (mask 13) (6156 * 13) (J3BetaP 9) := (gen (j := 1) (by norm_num)).1
  unfold j3MemOK
  rw [beta_tab (k := 8) (by norm_num), beta_tab (k := 9) (by norm_num),
    beta_tab (k := 7) (by norm_num), cent_eq (by norm_num), ← Nat.eq_of_beq_eq_true hc]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, tblEq_self c8⟩
  · unfold CFSG.Sporadic.SmallOddCore.j3Sift
    rw [natArr_tabT c8]
    exact J3KT.sift_of ht
  · unfold CFSG.Sporadic.SmallOddCore.j3Sift
    rw [natArr_tabT c9]
    exact J3KT.sift_of hd
  · unfold CFSG.Sporadic.SmallOddCore.j3Sift
    rw [natArr_tabT hbc]
    exact J3KT.sift_of hb

end CertificateChecks.KernelSpor.B24603

end
