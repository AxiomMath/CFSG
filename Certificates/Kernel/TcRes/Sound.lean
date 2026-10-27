
module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RRows
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import Certificates.Kernel.TcRes.Glue
public import CFSG.Certificates.Kernel.TcRes.LeafSound
public import CFSG.Certificates.Kernel.TcRes.KerSound
public import CFSG.Certificates.Kernel.TcRes.ConjSound
public import CFSG.Certificates.Kernel.TcRes.C1Glue
public import CFSG.Certificates.Kernel.TcRes.MovedAnaSound
public import CFSG.Certificates.Kernel.TcRes.LabSound
public import CFSG.Certificates.Kernel.TcRes.SkewSound
public import CFSG.Certificates.Kernel.TcRes.C3BodySound
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC3FlagFree
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC3Roots
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC1Neg
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFlag
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFive
public import CFSG.Certificates.Kernel.TcRes.C3TreeSound

public section

namespace CFSG.KC.TcRes

open CFSG.KD.TcRes CFSG.KD.TcRes.ch715750glue CFSG.TcRes.TK CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TableCRes Certificates.TcRes
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso)

open CFSG.KC.TcRes.Lane in
theorem swOK_rec {U RC L M LF : ℕ → ℕ} {REPS START q : ℕ}
    (hsw : swOK U RC L M LF REPS START q = true) :
    ∀ p, fld START 16 q ≤ p → p < fld START 16 (q + 1) →
      p < fld START 16 75 ∧ pq (prec LF p) = q := by
  simp only [swOK, strictB_eq, andB_eq_true, nsub, Nat.succ_eq_add_one] at hsw
  have key : ∀ c p prev, swWalk L M LF (kq U RC REPS q) q (fld START 16 75) c p prev = true →
      ∀ t < c, p + t < fld START 16 75 ∧ pq (prec LF (p + t)) = q := by
    intro c
    induction c with
    | zero => intro p prev _ t ht; omega
    | succ c ih =>
      intro p prev h t ht
      change swStep L M LF (kq U RC REPS q) q (fld START 16 75) p prev
        (swWalk L M LF (kq U RC REPS q) q (fld START 16 75) c (p + 1)) = true at h
      simp only [swStep, strictB_eq, andB_eq_true, blt_eq_true, beq_eq_true, nadd, nmul] at h
      rcases t with _ | t
      · exact ⟨by simpa using h.1, by simpa using h.2.1⟩
      · have := ih (p + 1) _ h.2.2.2.2.2.2 t (by omega)
        rw [show p + 1 + t = p + (t + 1) by omega] at this
        exact this
  intro p hap hpe
  have := key _ _ _ hsw.2 (p - fld START 16 q) (by omega)
  rwa [show fld START 16 q + (p - fld START 16 q) = p by omega] at this

theorem c1_tot : fld C1P.START 16 75 ≤ 1872 := by decide +kernel

theorem rep23_id : ∀ m < 6, tf (Nat.land (Nat.shiftRight C1.REPS (23 * 42)) M42) m = m := by
  decide +kernel

theorem c1_neg_mem {τ : Tag}
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) : -α ∈ componentRoots χ i := by
  obtain ⟨hα', rfl⟩ := hα
  have hneg : -α ∈ kernelRoots χ := ⟨IsRoot.neg hα'.1, chi_neg hα'.2⟩
  refine ⟨hneg, (mk_eq_of_iform_ne_zero (α := ⟨α, hα'⟩) (β := ⟨-α, hneg⟩) ?_).symm⟩
  change iform α (-α) ≠ 0
  rw [iform_neg_right]
  exact neg_ne_zero.2 (iform_self_pos_of_isRoot hα'.1).ne'

theorem tcDataOK_conj {τ : Tag}
    (g : WeylGroup τ) {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    {d : TcrCData} (h : TcDataOK (tcrConjPerm g ρ) ((fun γ => g • γ) '' Ψ) d) :
    TcDataOK ρ Ψ d := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, componentOrbitLength_conj]
  · rw [h2, compRank_image]
  · rw [h3, Set.ncard_image_of_injective _ (MulAction.injective g)]
  · rw [← twistKindOf_conj g ρ Ψ]
    exact h4

theorem olen_ge (ph : ℕ → ℕ) (psi : ℕ) :
    ∀ n x s, olen ph psi n x s = 0 ∨ s ≤ olen ph psi n x s := by
  intro n
  induction n with
  | zero => exact fun _ _ => Or.inl rfl
  | succ n ih =>
    intro x s
    have e : olen ph psi (n + 1) x s = strictN (ph x) (fun y => Bool.rec (motive := fun _ => ℕ)
        (olen ph psi n y (s + 1)) s (bit psi y)) := rfl
    rw [e, CFSG.KC.TcRes.strictN_eq]
    cases bit psi (ph x)
    · rcases ih (ph x) (s + 1) with h | h
      · exact Or.inl h
      · exact Or.inr (by change s ≤ olen ph psi n (ph x) (s + 1); omega)
    · exact Or.inr le_rfl

theorem olen_one {ph : ℕ → ℕ} {psi n x : ℕ} (h : olen ph psi n x 1 = 1) :
    bit psi (ph x) = true := by
  cases n with
  | zero => exact absurd h Nat.zero_ne_one
  | succ n =>
    have e : olen ph psi (n + 1) x 1 = strictN (ph x) (fun y => Bool.rec (motive := fun _ => ℕ)
        (olen ph psi n y 2) 1 (bit psi y)) := rfl
    rw [e, CFSG.KC.TcRes.strictN_eq] at h
    cases hb : bit psi (ph x)
    · rw [hb] at h
      change olen ph psi n (ph x) 2 = 1 at h
      rcases olen_ge ph psi n (ph x) 2 with h' | h' <;> omega
    · rfl

open CFSG.KC.TcRes.Lane in
theorem mleaf_walk {W T M : ℕ} {ok : ℕ → Bool} : ∀ n p rest,
    Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
      (fun _ ih p rest => CFSG.TcRes.TK.strictB (Nat.land rest M) fun e =>
        CFSG.TcRes.TK.andB (CFSG.TcRes.TK.orB (Nat.ble T p) (ok e))
          (ih (Nat.succ p) (Nat.shiftRight rest W))) n p rest = true →
    ∀ i < n, p + i < T → ok (Nat.land (Nat.shiftRight rest (W * i)) M) = true := by
  intro n
  induction n with
  | zero => intro _ _ _ i hi; omega
  | succ n ih =>
    intro p rest h i hi hpi
    change CFSG.TcRes.TK.strictB (Nat.land rest M) (fun e =>
      CFSG.TcRes.TK.andB (CFSG.TcRes.TK.orB (Nat.ble T p) (ok e))
      (Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
        (fun _ ih p rest => CFSG.TcRes.TK.strictB (Nat.land rest M) fun e =>
          CFSG.TcRes.TK.andB (CFSG.TcRes.TK.orB (Nat.ble T p) (ok e))
            (ih (Nat.succ p) (Nat.shiftRight rest W)))
        n (Nat.succ p) (Nat.shiftRight rest W))) = true at h
    rw [strictB_eq, andB_eq_true] at h
    rcases i with _ | i
    · have h1 := h.1
      rw [orB_eq_true, ble_eq_true] at h1
      rcases h1 with h1 | h1
      · omega
      · simpa using h1
    · have := ih (Nat.succ p) (Nat.shiftRight rest W) h.2 i (by omega) (by omega)
      rw [nshr, nshr, ← Nat.shiftRight_add, show W + W * i = W * (i + 1) by ring] at this
      exact this

open CFSG.KC.TcRes.Lane in
theorem ml_of_leaf {RT X Y ADJ POS DEC NEG PW START : ℕ} {RC LS LF AS : ℕ → ℕ}
    (hleaf : ∀ L < 117, mleaf RT X Y ADJ POS DEC NEG PW RC LS LF AS START L = true) {p : ℕ}
    (hp : p < fld START 16 75) (hp' : p < 1872) :
    Nat.beq (Nat.land (Nat.shiftRight (prec LF p) 27) 1) 0 = true ∨
      anaOK RT X Y ADJ POS DEC NEG PW RC LS (prec LF p)
        (AS (Nat.land (Nat.shiftRight (prec LF p) 28) 255)) = true := by
  have hl := hleaf (p / 16) (by omega)
  rw [mleaf, strictB_eq] at hl
  have h := mleaf_walk (W := 547) (T := fld START 16 75) (M := M547)
    (ok := fun e => orB (Nat.beq (Nat.land (Nat.shiftRight e 27) 1) 0)
      (anaOK RT X Y ADJ POS DEC NEG PW RC LS e (AS (Nat.land (Nat.shiftRight e 28) 255))))
    16 _ _ hl (p % 16) (Nat.mod_lt _ (by norm_num)) (by
      change p / 16 * 16 + p % 16 < fld START 16 75
      omega)
  have e1 : Nat.shiftRight p 4 = p / 16 := by rw [nshr, Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land p 15 = p % 16 := by
    rw [nland]
    exact Nat.and_two_pow_sub_one_eq_mod p 4
  have e3 : prec LF p = Nat.land (Nat.shiftRight (LF (p / 16)) (547 * (p % 16))) M547 := by
    change Nat.land (Nat.shiftRight (LF (Nat.shiftRight p 4)) (Nat.mul (Nat.land p 15) 547))
      M547 = _
    rw [e1, e2, nmul, mul_comm]
  rw [e3]
  exact orB_eq_true.1 h

@[expose] noncomputable def linN (u1 u2 c n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun m ih => strictN ih fun a => Nat.add a (Nat.mul (Nat.pow (nat_lit 3) m)
      (Nat.mod (Nat.add (dg u1 m) (Nat.mul c (dg u2 m))) (nat_lit 3)))) n

theorem linN_succ (u1 u2 c n : ℕ) :
    linN u1 u2 c (n + 1) = linN u1 u2 c n + 3 ^ n * ((dg u1 n + c * dg u2 n) % 3) := by
  have e : linN u1 u2 c (n + 1) = strictN (linN u1 u2 c n) fun a => Nat.add a
      (Nat.mul (Nat.pow 3 n) (Nat.mod (Nat.add (dg u1 n) (Nat.mul c (dg u2 n))) 3)) := rfl
  rw [e, CFSG.KC.TcRes.strictN_eq]
  rfl

theorem linN_lt (u1 u2 c : ℕ) : ∀ n, linN u1 u2 c n < 3 ^ n := by
  intro n
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    rw [linN_succ, pow_succ]
    have : (dg u1 n + c * dg u2 n) % 3 ≤ 2 := by omega
    nlinarith [Nat.mul_le_mul_left (3 ^ n) this]

theorem dg_linN (u1 u2 c : ℕ) : ∀ n, ∀ m < n,
    dg (linN u1 u2 c n) m = (dg u1 m + c * dg u2 m) % 3 := by
  have hdg : ∀ x m, dg x m = x / 3 ^ m % 3 := fun _ _ => rfl
  intro n
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    intro m hm
    rw [linN_succ, hdg]
    rcases Nat.lt_or_ge m n with h | h
    · have e : 3 ^ n * ((dg u1 n + c * dg u2 n) % 3) =
          3 ^ m * (3 * (3 ^ (n - m - 1) * ((dg u1 n + c * dg u2 n) % 3))) := by
        rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_add]
        congr 2
        omega
      rw [e, Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num : 0 < 3)),
        Nat.add_mul_mod_self_left, ← hdg, ih m h]
    · have hmn : m = n := by omega
      subst hmn
      rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num : 0 < 3)),
        Nat.div_eq_of_lt (linN_lt u1 u2 c m), zero_add, Nat.mod_mod]

theorem v3_lin (u1 u2 c : ℕ) : v3 (lin u1 u2 c) = v3 u1 + (c : ZMod 3) • v3 u2 := by
  funext m
  have e : lin u1 u2 c = linN u1 u2 c 6 := rfl
  change (dg (lin u1 u2 c) m : ZMod 3) = (dg u1 m : ZMod 3) + (c : ZMod 3) * (dg u2 m : ZMod 3)
  rw [e, dg_linN u1 u2 c 6 m m.2, ZMod.natCast_mod]
  push_cast
  ring

theorem cover4 {P : Submodule (ZMod 3) (Fin 6 → ZMod 3)} {u1 u2 : Fin 6 → ZMod 3}
    (hP : ∀ v, v ∈ P ↔ ∃ s t : ZMod 3, v = s • u1 + t • u2) (xv : ℕ → Fin 6 → ZMod 3)
    (h0 : xv 0 = u1) (h1 : xv 1 = u2) (h2 : xv 2 = u1 + u2) (h3 : xv 3 = u1 + (2 : ZMod 3) • u2) :
    ∀ v ∈ P, v ≠ 0 → ∃ y < 4, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • xv y := by
  intro v hv hv0
  obtain ⟨s, t, rfl⟩ := (hP v).1 hv
  have key : ∀ (a b : ZMod 3) (y : ℕ), xv y = a • u1 + b • u2 → ∀ c : ZMod 3,
      (∀ m n : ZMod 3, s * m + t * n = c * (a * m + b * n)) →
      s • u1 + t • u2 = c • xv y := by
    intro a b y hy c hc
    rw [hy]
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hc _ _
  have h3' : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
  rcases h3' s with rfl | rfl | rfl <;> rcases h3' t with rfl | rfl | rfl
  · exact absurd (by simp) hv0
  · exact ⟨1, by norm_num, 1, by decide, key 0 1 1 (by rw [h1]; simp) 1 (by decide)⟩
  · exact ⟨1, by norm_num, 2, by decide, key 0 1 1 (by rw [h1]; simp) 2 (by decide)⟩
  · exact ⟨0, by norm_num, 1, by decide, key 1 0 0 (by rw [h0]; simp) 1 (by decide)⟩
  · exact ⟨2, by norm_num, 1, by decide, key 1 1 2 (by rw [h2]; simp) 1 (by decide)⟩
  · exact ⟨3, by norm_num, 1, by decide, key 1 2 3 (by rw [h3]; simp) 1 (by decide)⟩
  · exact ⟨0, by norm_num, 2, by decide, key 1 0 0 (by rw [h0]; simp) 2 (by decide)⟩
  · exact ⟨3, by norm_num, 2, by decide, key 1 2 3 (by rw [h3]; simp) 2 (by decide)⟩
  · exact ⟨2, by norm_num, 2, by decide, key 1 1 2 (by rw [h2]; simp) 2 (by decide)⟩

theorem c1_lines {P : Submodule (ZMod 3) (Fin 6 → ZMod 3)} {a b : ℕ}
    (hred : IsReduced (v3 a) (v3 b))
    (hP : ∀ v, v ∈ P ↔ ∃ s t : ZMod 3, v = s • v3 a + t • v3 b) :
    (∀ y < 4, v3 (xs a b y) ∈ P ∧ v3 (xs a b y) ≠ 0) ∧
      ∀ v ∈ P, v ≠ 0 → ∃ y < 4, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • v3 (xs a b y) := by
  have e2 : v3 (xs a b 2) = v3 a + v3 b := by
    change v3 (lin a b 1) = _
    rw [v3_lin, Nat.cast_one, one_smul]
  have e3 : v3 (xs a b 3) = v3 a + (2 : ZMod 3) • v3 b := by
    change v3 (lin a b 2) = _
    rw [v3_lin, Nat.cast_ofNat]
  refine ⟨fun y hy => ?_, cover4 hP (fun y => v3 (xs a b y)) rfl rfl e2 e3⟩
  have key : ∀ s t : ZMod 3, (s ≠ 0 ∨ t ≠ 0) → v3 (xs a b y) = s • v3 a + t • v3 b →
      v3 (xs a b y) ∈ P ∧ v3 (xs a b y) ≠ 0 := by
    intro s t hst h
    refine ⟨(hP _).2 ⟨s, t, h⟩, fun h0 => ?_⟩
    have := hred.indep (h.symm.trans h0)
    rcases hst with h1 | h1
    · exact h1 this.1
    · exact h1 this.2
  interval_cases y
  · exact key 1 0 (Or.inl (by decide)) (by simp; rfl)
  · exact key 0 1 (Or.inr (by decide)) (by simp; rfl)
  · exact key 1 1 (Or.inl (by decide)) (by rw [e2]; simp)
  · exact key 1 2 (Or.inl (by decide)) (by rw [e3]; simp)

theorem e6Dv : DatumRaw Tag.E6 72 (vecOf Tag.E6.rank E6.V) (fun g v => rtv E6.RT g v)
    (fun g v => Nat.beq (fld (fld E6.ADJ 72 g) 1 v) 1) (fun i => fld E6.NEG 7 i) :=
  { e6D with
    refl := fun g hg v hv => by
      rw [rtv_eq_fld _ _ _ hv]
      exact e6D.refl g hg v hv }

theorem e6_ycl' : ∀ m < 6, ∀ j < 12, fld (E6.yc m) 16 j ≤ 3 := by decide +kernel

theorem e6_hX : ∀ v < 72, ∀ g < 72, (CFSG.TcRes.TK.dP 6 (fld E6.X 192 v * fld E6.Y 192 g) : ℤ) -
    dQ 6 (fld E6.X 192 v * fld E6.Y 192 g) =
      iform (vecOf Tag.E6.rank E6.V v) (vecOf Tag.E6.rank E6.V g) :=
  iform_of_checks Tag.E6 e6_yc e6_ycb (fun m j => by
    rcases Nat.lt_or_ge j 12 with h | h
    · exact e6_ycl' m.1 m.2 j h
    · rw [CFSG.KC.TcRes.Lane.fld_eq_zero_of_lt 16 12 _
        (lt_of_lt_of_eq (e6_ycb m) rfl) h]
      omega) ch715750all.e6_root

theorem c1_ls_hi : ∀ l < 22, C1M.LS (234 + l) = 0 := by decide +kernel

theorem c1_hls : ∀ l < 256, C1M.LS l = 0 ∨ lineOK E6.RT E6.X E6.Y E6.ADJ C1M.POS C1M.DEC E6.NEG
    C1P.PW C1P.rcS (C1M.LS l) = true := by
  intro l hl
  rcases Nat.lt_or_ge l 234 with h | h
  · exact Or.inr (ch715750all.m_line l h)
  · left
    have := c1_ls_hi (l - 234) (by omega)
    rwa [Nat.add_sub_cancel' h] at this

open CFSG.KC.TcRes.Lane in
theorem c1_rep_surv {q : ℕ}
    (hq : q < 75) (h70 : q ≠ 70) (h71 : q ≠ 71) {w : WeylGroup Tag.E6}
    (hw : TupleOf (vecOf Tag.E6.rank E6.V) 72
      (Nat.land (Nat.shiftRight C1.REPS (q / 3 * 42)) M42) w)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = c1Eps (q % 3) • (w • γ)) {r : ℕ}
    (hr : ((c1Eps (q % 3) : ℤ) : ZMod 3) * (sOf (q % 3) : ZMod 3) = r)
    {F f' : ℕ} (hf' : f' ∈ c1Flags (q % 3)) (hflag : FlagTransfer 3 F f')
    (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)) (hP2 : Module.finrank (ZMod 3) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = (r : ZMod 3) * v j)
    (iJ : KernelComponent (tcChiPl Tag.E6 3 P)) {x : Fin Tag.E6.rank → ZMod 3}
    (ix : KernelComponent (tcChiLn Tag.E6 3 x)) (hS : SurvHyp ρ F P iJ x ix) :
    ∃ dJ dx : TcrCData, TcDataOK ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ) dJ ∧
      TcDataOK ρ (componentRoots (tcChiLn Tag.E6 3 x) ix) dx ∧
      tcrAllowedC1 (c1Eps (q % 3)) f' dJ dx = true := by
  classical
  have hε : c1Eps (q % 3) = 1 ∨ c1Eps (q % 3) = -1 := by
    unfold c1Eps
    split_ifs <;> simp
  have hK : ∀ v ∈ P, v ∈ KSet w (sOf (q % 3) : ZMod 3) := kset_of_frob hε hρ hr P hfrob
  obtain ⟨p, hap, hpe, -, -, hred, hspan⟩ := (c1_sweep hq h70 h71 hw).exists_record hP2 hK
  obtain ⟨hptot, hpq⟩ := swOK_rec (ch715750all.p_sw q hq h70 h71) p hap hpe
  have hpl : plOK C1P.rcS E6.ADJ C1P.PW E6.NEG (prec C1P.LF p) = true :=
    pl_of_leaf ch715750all.p_leaf hptot (lt_of_lt_of_le hptot c1_tot)
  let φ : AddMonoid.End (Fin Tag.E6.rank → ℤ) :=
    c1Eps (q % 3) • DistribMulAction.toAddMonoidEnd (WeylGroup Tag.E6) (Fin Tag.E6.rank → ℤ) w
  have hφ : ∀ γ, φ γ = c1Eps (q % 3) • (w • γ) := fun γ => rfl
  have hρφ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = φ γ := fun γ hγ => (hρ γ hγ).trans (hφ γ).symm
  have hφr : ∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (φ γ) := by
    intro γ hγ
    rw [hφ]
    rcases hε with h | h <;> rw [h]
    · rw [one_smul]
      exact IsRoot.smul hγ w
    · rw [neg_one_smul]
      exact IsRoot.neg (IsRoot.smul hγ w)
  have hiso : ∀ x y, iform (φ x) (φ y) = iform x y := by
    intro x y
    rw [hφ, hφ, ← iform_smul w x y]
    rcases hε with h | h <;> rw [h]
    · simp only [one_smul]
    · simp only [neg_one_smul, iform_neg_right]
      simp [iform, Finset.sum_neg_distrib]
  have hph : ∀ g < 72, vecOf Tag.E6.rank E6.V (phq C1P.PW E6.NEG q g) =
      φ (vecOf Tag.E6.rank E6.V g) := by
    intro g hg
    rw [(phq_spec e6D ch715750all.e6_root ch715750all.p_pw hq hw g hg).2, hφ, c1Eps]
    by_cases h0 : q % 3 = 0
    · rw [if_pos h0, if_pos h0, one_smul]
    · rw [if_neg h0, if_neg h0, neg_one_smul]
  have hΦ : ∀ g, g ∈ PhiP (vecOf Tag.E6.rank E6.V) (v3 (pu1 (prec C1P.LF p)))
      (v3 (pu2 (prec C1P.LF p))) ↔ g < 72 ∧ ∀ v ∈ (P : Set (Fin Tag.E6.rank → ZMod 3)),
        ∑ m, v m * ((vecOf Tag.E6.rank E6.V g m : ℤ) : ZMod 3) = 0 := by
    intro g
    exact and_congr_right fun _ => (plane_cond hspan
      (fun m => ((vecOf Tag.E6.rank E6.V g m : ℤ) : ZMod 3))).symm
  have hmv01 : Nat.land (Nat.shiftRight (prec C1P.LF p) 27) 1 = 0 ∨
      Nat.land (Nat.shiftRight (prec C1P.LF p) 27) 1 = 1 := by
    have : Nat.land (Nat.shiftRight (prec C1P.LF p) 27) 1 < 2 := by
      rw [nland]
      exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
    omega
  rcases hmv01 with hmv | hmv
  ·
    exfalso
    have hrec := planeRec_of_checks rfl e6D ch715750all.p_rc hpl hmv
    rw [hpq] at hrec
    have h1 := orbitLength_one_of_rec e6D φ ρ hρφ hφr hiso (r : ZMod 3) P hfrob _ hΦ hph
      (fun g hg => by
        obtain ⟨r', hr', h1, h2⟩ := hrec g hg
        exact ⟨r', hr', h1, h2⟩) iJ
    have h2 := hS.1
    omega
  ·
    have hana := (ml_of_leaf ch715750all.m_leaf hptot (lt_of_lt_of_le hptot c1_tot)).resolve_left
      (by rw [hmv]; decide)
    have hblk := anaBlocks_of_checks e6D (kmask_lt _ _ _) hpl hana
    rw [hpq] at hblk
    have hmk : mset 72 (kmask C1P.rcS (pu1 (prec C1P.LF p)) (pu2 (prec C1P.LF p))) =
        PhiP (vecOf Tag.E6.rank E6.V) (v3 (pu1 (prec C1P.LF p))) (v3 (pu2 (prec C1P.LF p))) :=
      mset_kmask ch715750all.p_rc (pu1 (prec C1P.LF p)) (pu2 (prec C1P.LF p))
    have himg := image_eq_kernelRoots e6D (P : Set (Fin Tag.E6.rank → ZMod 3)) _ hΦ
    rw [← hmk] at himg
    have hker := kernelRoots_frob_image φ ρ hρφ hφr (r : ZMod 3)
      (P : Set (Fin Tag.E6.rank → ZMod 3)) hfrob
    have hform : ∀ α ∈ kernelRoots (tcChiPl Tag.E6 3 P), ∀ β ∈ kernelRoots (tcChiPl Tag.E6 3 P),
        iform (ρ α) (ρ β) = iform α β := by
      intro α hα β hβ
      rw [hρφ _ ((mem_kernelRoots_chiQ 3 _ α).1 hα).1, hρφ _ ((mem_kernelRoots_chiQ 3 _ β).1 hβ).1,
        hiso]
    obtain ⟨γ0, hγ0⟩ : ∃ γ0, γ0 ∈ componentRoots (tcChiPl Tag.E6 3 P) iJ := by
      obtain ⟨y, rfl⟩ := Quotient.exists_rep iJ
      exact ⟨y.1, y.2, rfl⟩
    obtain ⟨g0, hg0, rfl⟩ : γ0 ∈ vecOf Tag.E6.rank E6.V '' mset 72
        (kmask C1P.rcS (pu1 (prec C1P.LF p)) (pu2 (prec C1P.LF p))) := by
      rw [himg]
      exact hγ0.1
    obtain ⟨C, rt, hg0C, hrtC, hCΦ, hconn, hcl, holen0, holen⟩ := hblk g0 hg0
    obtain ⟨i, hi⟩ := exists_componentRoots_eq_image himg hCΦ hrtC hconn hcl
    have hiJ : i = iJ := eq_of_mem_componentRoots (hi ▸ Set.mem_image_of_mem _ hg0C) hγ0
    subst hiJ
    rcases holen with h1 | ⟨jb, hjb⟩
    ·
      exfalso
      have hrN : rt < 72 := ((hCΦ hrtC : rt ∈ mset 72 _)).1
      have hin : phq C1P.PW E6.NEG q rt ∈ mset 72 C :=
        ⟨(phq_spec e6D ch715750all.e6_root ch715750all.p_pw hq hw rt hrN).1, olen_one h1⟩
      have h1' : componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) i) = 1 := by
        refine componentOrbitLength_eq_of_first ρ hker hform i (γ := vecOf Tag.E6.rank E6.V rt)
          (by rw [hi]; exact Set.mem_image_of_mem _ hrtC) one_pos ?_ (fun s hs hs' => by omega)
        rw [Function.iterate_one, hρφ _ (e6D.isRoot rt hrN), ← hph rt hrN, hi]
        exact Set.mem_image_of_mem _ hin
      have h2 := hS.1
      omega
    ·
      have hphN : ∀ g < 72, phq C1P.PW E6.NEG q g < 72 :=
        fun g hg => (phq_spec e6D ch715750all.e6_root ch715750all.p_pw hq hw g hg).1
      obtain ⟨dJ, r0, hcJ, hkJ, -, E0, E1, E2, E3, hlines, hjok⟩ := jbOK_spec (V := E6.V) rfl e6Dv
        e6_hX ch715750all.m_pos ch715750all.m_dec hphN
        (by
          rintro Φ' (rfl | ⟨x', rfl⟩)
          · exact sub_mem_kmask ch715750all.p_rc _ _
          · exact sub_mem_kv ch715750all.p_rc x')
        c1_hls hjb
      have hsym1 : ∀ i, Tag.E6.symmetrizer i i = 1 := fun i => by simp [Tag.symmetrizer]
      have hρv : ∀ g < 72, ρ (vecOf Tag.E6.rank E6.V g) = φ (vecOf Tag.E6.rank E6.V g) :=
        fun g hg => hρφ _ (e6D.isRoot g hg)
      obtain ⟨iJ', hiJ', hdJ⟩ := tcDataOK_of_compRaw e6Dv hsym1 ρ φ hker hform himg hphN hph
        hρv hcJ hkJ
      have hiJ'' : iJ' = i := eq_of_mem_componentRoots
        (hiJ' ▸ Set.mem_image_of_mem _ hrtC) (hi ▸ Set.mem_image_of_mem _ hrtC)
      rw [hiJ''] at hdJ
      obtain ⟨hxv, hcover⟩ := c1_lines hred hspan
      have hlc : ∀ y < 4, ∃ iy : KernelComponent (tcChiLn Tag.E6 3
          (v3 (xs (pu1 (prec C1P.LF p)) (pu2 (prec C1P.LF p)) y))),
          componentRoots _ iy = vecOf Tag.E6.rank E6.V '' mset 72
            (sel4 (leP E0) (leP E1) (leP E2) (leP E3) y) ∧
          TcDataOK ρ (componentRoots _ iy) (tkCd (sel4 (leD E0) (leD E1) (leD E2) (leD E3) y)) := by
        intro y hy
        obtain ⟨hxe, -, ⟨g1, r1, hc1⟩, hk1⟩ := hlines y hy
        set x' := xs (pu1 (prec C1P.LF p)) (pu2 (prec C1P.LF p)) y with hx'
        have hΦx : ∀ g, g ∈ mset 72 (kv C1P.rcS x') ↔ g < 72 ∧
            ∀ v ∈ ({v3 x'} : Set (Fin Tag.E6.rank → ZMod 3)),
              ∑ m, v m * ((vecOf Tag.E6.rank E6.V g m : ℤ) : ZMod 3) = 0 := by
          intro g
          rw [mset_kv ch715750all.p_rc x']
          exact and_congr_right fun _ => ⟨fun h v hv => by
            have hv' : v = v3 x' := hv
            rw [hv']
            exact h, fun h => h _ rfl⟩
        have himgx := image_eq_kernelRoots e6D ({v3 x'} : Set (Fin Tag.E6.rank → ZMod 3)) _ hΦx
        have hkerx := kernelRoots_frob_image φ ρ hρφ hφr (r : ZMod 3)
          ({v3 x'} : Set (Fin Tag.E6.rank → ZMod 3)) (fun v hv => by
            have hv' : v = v3 x' := hv
            rw [hv']
            exact hfrob _ (hxv y hy).1)
        have hformx : ∀ α ∈ kernelRoots (tcChiLn Tag.E6 3 (v3 x')),
            ∀ β ∈ kernelRoots (tcChiLn Tag.E6 3 (v3 x')), iform (ρ α) (ρ β) = iform α β := by
          intro α hα β hβ
          rw [hρφ _ ((mem_kernelRoots_chiQ 3 _ α).1 hα).1,
            hρφ _ ((mem_kernelRoots_chiQ 3 _ β).1 hβ).1, hiso]
        obtain ⟨iy, hiy, hdy⟩ := tcDataOK_of_compRaw e6Dv hsym1 ρ φ hkerx hformx himgx hphN hph
          hρv hc1 hk1
        refine ⟨iy, ?_, ?_⟩
        · rw [sel4_map leP] at hiy
          exact hiy
        · rw [← sel4_map leD]
          exact hdy
      choose ix' hix' hdx' using hlc
      obtain ⟨y, hy, hΨy, hΨne, hspl, hrest⟩ := surv_lines hflag P i hdJ
        (γ0 := vecOf Tag.E6.rank E6.V rt) (by rw [hi]; exact Set.mem_image_of_mem _ hrtC)
        (n := 4) (fun y => v3 (xs (pu1 (prec C1P.LF p)) (pu2 (prec C1P.LF p)) y)) hxv hcover
        (fun y => vecOf Tag.E6.rank E6.V '' mset 72 (sel4 (leP E0) (leP E1) (leP E2) (leP E3) y))
        (fun y => tkCd (sel4 (leD E0) (leD E1) (leD E2) (leD E3) y))
        (fun y hy => ⟨ix' y hy, (hix' y hy).symm⟩)
        (fun y hy => by
          have := (hlines y hy).g0_mem
          rw [sel4_map leP] at this
          exact Set.mem_image_of_mem _ this)
        (fun y hy => by rw [← hix' y hy]; exact hdx' y hy)
        hS.2.1 hS.2.2.1 ix hS.2.2.2.1 hS.2.2.2.2.1 hS.2.2.2.2.2.1 hS.2.2.2.2.2.2
      have hps : sel4 (leP E0) (leP E1) (leP E2) (leP E3) y ≠ C := by
        intro h
        apply hΨne
        simp only [h, hi]
      have hal := jok_spec hjok f' hf' y hy hps hspl hrest
      refine ⟨tkCd dJ, tkCd (sel4 (leD E0) (leD E1) (leD E2) (leD E3) y), hdJ, ?_, hal⟩
      rw [← hΨy, ← hix' y hy]
      exact hdx' y hy

theorem c1_surv {b : ℕ} (hb : b < 3)
    (w : WeylGroup Tag.E6) {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = c1Eps b • (w • γ)) {r : ℕ}
    (hr : ((c1Eps b : ℤ) : ZMod 3) * (sOf b : ZMod 3) = r)
    {F f' : ℕ} (hf' : f' ∈ c1Flags b) (hflag : FlagTransfer 3 F f')
    (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)) (hP2 : Module.finrank (ZMod 3) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = (r : ZMod 3) * v j)
    (iJ : KernelComponent (tcChiPl Tag.E6 3 P)) {x : Fin Tag.E6.rank → ZMod 3}
    (ix : KernelComponent (tcChiLn Tag.E6 3 x)) (hS : SurvHyp ρ F P iJ x ix) :
    ∃ dJ dx : TcrCData, TcDataOK ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ) dJ ∧
      TcDataOK ρ (componentRoots (tcChiLn Tag.E6 3 x) ix) dx ∧
      tcrAllowedC1 (c1Eps b) f' dJ dx = true := by
  obtain ⟨k, hk, w', hw', hconj⟩ := e6_conj_rep w
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hw'eq : c⁻¹ * w * c⁻¹⁻¹ = w' := by
    rw [← hc]
    group
  generalize c⁻¹ = h at hw'eq
  let φ : AddMonoid.End (Fin Tag.E6.rank → ℤ) :=
    c1Eps b • DistribMulAction.toAddMonoidEnd (WeylGroup Tag.E6) (Fin Tag.E6.rank → ℤ) w
  have hφ : ∀ γ, φ γ = c1Eps b • (w • γ) := fun γ => rfl
  have hρφ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = φ γ := fun γ hγ => (hρ γ hγ).trans (hφ γ).symm
  have hρ' : ∀ γ, IsRoot Tag.E6 γ → tcrConjPerm h ρ γ = c1Eps b • (w' • γ) := by
    intro γ hγ
    rw [tcrConjPerm_apply, hρ _ (IsRoot.smul hγ h⁻¹), smul_comm, ← hw'eq, mul_smul, mul_smul]
  obtain ⟨iJ', ix', hJ', hx', hS'⟩ := SurvHyp.conj h hS
  have hfrob' := tcrDual_frob h φ ρ hρφ (r : ZMod 3) P hfrob
  have hP2' : Module.finrank (ZMod 3) (P.map (tcrDualLin h 3)) = 2 := by
    rw [finrank_map_tcrDualLin]
    exact hP2
  have hq3 : (3 * k + b) % 3 = b := by omega
  have hq : (3 * k + b) / 3 = k := by omega
  by_cases hid : 3 * k + b = 70 ∨ 3 * k + b = 71
  ·
    exfalso
    have hk23 : k = 23 := by omega
    have hb0 : b ≠ 0 := by omega
    subst hk23
    have hid' : ∀ γ : Fin Tag.E6.rank → ℤ, w' • γ = γ := by
      have he : ∀ j : Fin Tag.E6.rank, w' • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
          Pi.single j 1 := by
        intro j
        rw [← (hw' j).2, rep23_id j.1 j.2]
        exact e6D.simple j
      intro γ
      conv_lhs => rw [← Finset.univ_sum_single γ]
      conv_rhs => rw [← Finset.univ_sum_single γ]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : (Pi.single j (γ j) : Fin Tag.E6.rank → ℤ) = γ j • Pi.single j 1 := by
        funext m
        by_cases hm : m = j
        · subst hm
          simp
        · simp [Pi.single_apply, hm]
      rw [hs, smul_comm, he]
    have hneg : ∀ γ, IsRoot Tag.E6 γ → tcrConjPerm h ρ γ = -γ := by
      intro γ hγ
      rw [hρ' γ hγ, hid', c1Eps, if_neg hb0, neg_one_smul]
    have h1 : componentOrbitLength (tcrConjPerm h ρ)
        (componentRoots (tcChiPl Tag.E6 3 (P.map (tcrDualLin h 3))) iJ') = 1 := by
      refine componentOrbitLength_eq_one_of_neg
        (CFSG.StandardType.LieKnownR2.ExcPos.kernelRoots_finite.subset fun α hα => hα.1)
        (fun γ hγ => c1_neg_mem hγ) (fun γ hγ => hneg γ hγ.1.1)
    have h2 := hS'.1
    omega
  push Not at hid
  have hw'q : TupleOf (vecOf Tag.E6.rank E6.V) 72
      (Nat.land (Nat.shiftRight C1.REPS ((3 * k + b) / 3 * 42)) M42) w' := by
    rw [hq]
    exact hw'
  obtain ⟨dJ, dx, hdJ, hdx, hal⟩ := c1_rep_surv (q := 3 * k + b) (by omega) hid.1 hid.2 hw'q
    (fun γ hγ => by rw [hq3]; exact hρ' γ hγ) (by rw [hq3]; exact hr) (by rw [hq3]; exact hf')
    hflag _ hP2' hfrob' iJ' ix' hS'
  rw [hq3] at hal
  rw [hJ'] at hdJ
  rw [hx'] at hdx
  exact ⟨dJ, dx, tcDataOK_conj h hdJ, tcDataOK_conj h hdx, hal⟩

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TableCRes in
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit) in
open CFSG.StandardType (GGLabelIso) in
theorem certificate715750_of_checks :
 (∀ (w : WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)),
    (∀ γ, IsRoot Tag.E6 γ → ρ γ = w • γ) →
    ∀ {F : ℕ}, (F = 1 ∨ (3 ≤ F ∧ F % 2 = 1)) →
    ∀ (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)), Module.finrank (ZMod 3) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = 2 * v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E6 3 P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ) →
    ∀ {x : Fin Tag.E6.rank → ZMod 3}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E6 3 x)),
    componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 x) ix →
    componentRoots (tcChiLn Tag.E6 3 x) ix ≠ componentRoots (tcChiPl Tag.E6 3 P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
      LargeEvenSplit 3 lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i)) ∧
        LargeEvenHalfSplit 3 lab' c) →
    F = 1 ∧ TcC1Row ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ)
      (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
  (∀ (w : WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)),
    (∀ γ, IsRoot Tag.E6 γ → ρ γ = -(w • γ)) →
    ∀ {F : ℕ}, (F = 1 ∨ (3 ≤ F ∧ F % 2 = 1)) →
    ∀ (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)), Module.finrank (ZMod 3) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = 2 * v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E6 3 P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ) →
    ∀ {x : Fin Tag.E6.rank → ZMod 3}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E6 3 x)),
    componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 x) ix →
    componentRoots (tcChiLn Tag.E6 3 x) ix ≠ componentRoots (tcChiPl Tag.E6 3 P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
      LargeEvenSplit 3 lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i)) ∧
        LargeEvenHalfSplit 3 lab' c) →
    F = 1 ∧ TcC1RowNegOne ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ)
      (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
  (∀ (w : WeylGroup Tag.E6) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)),
    (∀ γ, IsRoot Tag.E6 γ → ρ γ = -(w • γ)) →
    ∀ {F : ℕ}, (2 ≤ F ∧ F % 2 = 0) →
    ∀ (P : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)), Module.finrank (ZMod 3) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E6.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 3) * v k = v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E6 3 P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ) →
    ∀ {x : Fin Tag.E6.rank → ZMod 3}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E6 3 x)),
    componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 x) ix →
    componentRoots (tcChiLn Tag.E6 3 x) ix ≠ componentRoots (tcChiPl Tag.E6 3 P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 x) ix)) ∧
      LargeEvenSplit 3 lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 3, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E6 3 d),
      componentRoots (tcChiPl Tag.E6 3 P) iJ ⊆ componentRoots (tcChiLn Tag.E6 3 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E6 3 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E6 3 d) i)) ∧
        LargeEvenHalfSplit 3 lab' c) →
    TcC1RowNegTwo ρ (componentRoots (tcChiPl Tag.E6 3 P) iJ)
      (componentRoots (tcChiLn Tag.E6 3 x) ix)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w ρ hρ F hF P hP2 hfrob iJ hJ2 x hxP hx0 ix hJx hne hsplit hoth
    have hS : SurvHyp ρ F P iJ x ix := ⟨hJ2, hxP, hx0, hJx, hne, hsplit, hoth⟩
    have hflag : FlagTransfer 3 F (if F = 1 then 1 else 3) := by
      by_cases h1 : F = 1
      · subst h1
        simpa using flagTransfer_refl 3 1
      · rw [if_neg h1]
        rcases hF with h | ⟨h3, h2⟩
        · exact absurd h h1
        · exact flagTransfer_three h2 h3
    obtain ⟨dJ, dx, hdJ, hdx, hal⟩ := c1_surv (b := 0) (by norm_num) w (r := 2)
      (fun γ hγ => by rw [hρ γ hγ]; simp [c1Eps]) (by decide)
      (by rw [show c1Flags 0 = [1, 3] from rfl]; split_ifs <;> simp) hflag P hP2
      (fun v hv j => by simpa using hfrob v hv j) iJ ix hS
    by_cases h1 : F = 1
    · rw [if_pos h1] at hal
      exact ⟨h1, tcC1_row_of_allowed hdJ hdx (by simpa [c1Eps] using hal)⟩
    · rw [if_neg h1] at hal
      simp [c1Eps, tcrAllowedC1_one_three] at hal
  · intro w ρ hρ F hF P hP2 hfrob iJ hJ2 x hxP hx0 ix hJx hne hsplit hoth
    have hS : SurvHyp ρ F P iJ x ix := ⟨hJ2, hxP, hx0, hJx, hne, hsplit, hoth⟩
    have hflag : FlagTransfer 3 F (if F = 1 then 1 else 3) := by
      by_cases h1 : F = 1
      · subst h1
        simpa using flagTransfer_refl 3 1
      · rw [if_neg h1]
        rcases hF with h | ⟨h3, h2⟩
        · exact absurd h h1
        · exact flagTransfer_three h2 h3
    obtain ⟨dJ, dx, hdJ, hdx, hal⟩ := c1_surv (b := 1) (by norm_num) w (r := 2)
      (fun γ hγ => by rw [hρ γ hγ]; simp [c1Eps]) (by decide)
      (by rw [show c1Flags 1 = [1, 3] from rfl]; split_ifs <;> simp) hflag P hP2
      (fun v hv j => by simpa using hfrob v hv j) iJ ix hS
    by_cases h1 : F = 1
    · rw [if_pos h1] at hal
      exact ⟨h1, tcC1_row_of_allowed_negOne hdJ hdx (by simpa [c1Eps] using hal)⟩
    · rw [if_neg h1] at hal
      simp [c1Eps, tcrAllowedC1_neg_one_three] at hal
  · intro w ρ hρ F hF P hP2 hfrob iJ hJ2 x hxP hx0 ix hJx hne hsplit hoth
    have hS : SurvHyp ρ F P iJ x ix := ⟨hJ2, hxP, hx0, hJx, hne, hsplit, hoth⟩
    obtain ⟨dJ, dx, hdJ, hdx, hal⟩ := c1_surv (b := 2) (by norm_num) w (r := 1)
      (fun γ hγ => by rw [hρ γ hγ]; simp [c1Eps]) (by decide) (f' := 2) (by simp [c1Flags])
      (flagTransfer_even hF.2 hF.1) P hP2
      (fun v hv j => by simpa using hfrob v hv j) iJ ix hS
    exact tcC1_row_of_allowed_negTwo hdJ hdx (by simpa [c1Eps] using hal)

theorem e8_ycl' : ∀ m < 8, ∀ j < 16, fld (E8.yc m) 16 j ≤ 3 := by decide +kernel

theorem e8_ycl : ∀ m : Fin Tag.E8.rank, ∀ j, fld (E8.yc m) 16 j ≤ 3 := fun m j => by
  rcases Nat.lt_or_ge j 16 with h | h
  · exact e8_ycl' m.1 m.2 j h
  · rw [CFSG.KC.TcRes.Lane.fld_eq_zero_of_lt 16 16 _ (lt_of_lt_of_eq (e8_ycb m) rfl) h]
    omega

theorem e8_hX : ∀ v < 240, ∀ g < 240, (CFSG.TcRes.TK.dP 8 (fld E8.X 256 v * fld E8.Y 256 g) : ℤ) -
    dQ 8 (fld E8.X 256 v * fld E8.Y 256 g) =
      iform (vecOf Tag.E8.rank E8.V v) (vecOf Tag.E8.rank E8.V g) :=
  iform_of_checks Tag.E8 e8_yc e8_ycb e8_ycl ch715750all.e8_root

theorem e8_qb : ∀ m < 8, E8T.QS m < 2 ^ (16 * 240) := by decide +kernel

theorem e8_ndb : E8T.ND < 2 ^ (288 * 550) := by decide +kernel

theorem c2_search :
    SearchRaw (vecOf Tag.E8.rank E8.V) E8T.ND E8T.T0 550 :=
  searchRaw_of_checks rfl e8D e8_hX
    (fun i hi m hm => (root_lanes (n := 8) (by norm_num) (ch715750all.e8_root i hi)).1 m hm)
    (fun g hg m => cart_row Tag.E8 e8_yc e8_ycb e8_ycl ch715750all.e8_root hg m)
    (fun g hg j => (root_lanes (n := 8) (by norm_num) (ch715750all.e8_root g hg)).2.2.1 j)
    e8_qb ch715750all.t_q ch715750all.t_mv e8_ndb ch715750all.t_nd ch715751t.root

open CFSG.KC.TcRes.Lane in
theorem sw5_rec {L M LF : ℕ → ℕ} {s : ℕ} (hsw : sw5OK L M LF s = true) :
    ∀ p, 806 * s ≤ p → p < 806 * s + 806 → Nat.land (Nat.shiftRight (prec5 LF p) 20) 1 = s := by
  simp only [sw5OK, andB_eq_true] at hsw
  have key : ∀ c p prev, sw5Walk L M LF s c p prev = true →
      ∀ t < c, Nat.land (Nat.shiftRight (prec5 LF (p + t)) 20) 1 = s := by
    intro c
    induction c with
    | zero => intro p prev _ t ht; omega
    | succ c ih =>
      intro p prev h t ht
      change CFSG.TcRes.TK.strictB (prec5 LF p) (fun e =>
        CFSG.TcRes.TK.strictB (Nat.land e 1023) fun c1 =>
        CFSG.TcRes.TK.strictB (Nat.land (Nat.shiftRight e 10) 1023) fun c2 =>
        CFSG.TcRes.TK.strictB (Nat.add (Nat.mul 625 c1) c2) fun key =>
          CFSG.TcRes.TK.andB (Nat.beq (Nat.land (Nat.shiftRight e 20) 1) s)
            (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.anyLt 4 fun j =>
              CFSG.TcRes.TK.andB (lane1 (L j) c2) (lane1 (M j) c1))
              (CFSG.TcRes.TK.andB (Nat.blt prev key) (sw5Walk L M LF s c (Nat.succ p) key))))
        = true at h
      simp only [strictB_eq, andB_eq_true, beq_eq_true] at h
      rcases t with _ | t
      · simpa using h.1
      · have := ih (p + 1) _ h.2.2.2 t (by omega)
        rw [show p + 1 + t = p + (t + 1) by omega] at this
        exact this
  intro p hap hpe
  have := key 806 (806 * s) 0 hsw.2 (p - 806 * s) (by omega)
  rwa [show 806 * s + (p - 806 * s) = p by omega] at this

open CFSG.KC.TcRes.Lane in
theorem ml8_of_leaf {ADJ POS DEC PW : ℕ} {RC BS LS LF AS : ℕ → ℕ}
    (hleaf : ∀ L < 101, mleaf8 ADJ POS DEC PW RC BS LS LF AS L = true) {p : ℕ} (hp : p < 1612) :
    Nat.beq (Nat.land (Nat.shiftRight (prec5 LF p) 21) 1) 0 = true ∨
      ana8OK ADJ POS DEC PW RC BS LS (prec5 LF p)
        (AS (Nat.land (Nat.shiftRight (prec5 LF p) 22) 4095)) = true := by
  have hl := hleaf (p / 16) (by omega)
  have h := mleaf_walk (W := 448) (T := 1612) (M := M448)
    (ok := fun e => orB (Nat.beq (Nat.land (Nat.shiftRight e 21) 1) 0)
      (ana8OK ADJ POS DEC PW RC BS LS e (AS (Nat.land (Nat.shiftRight e 22) 4095))))
    16 _ _ hl (p % 16) (Nat.mod_lt _ (by norm_num)) (by
      change p / 16 * 16 + p % 16 < 1612
      omega)
  have e1 : Nat.shiftRight p 4 = p / 16 := by rw [nshr, Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land p 15 = p % 16 := by
    rw [nland]
    exact Nat.and_two_pow_sub_one_eq_mod p 4
  have e3 : prec5 LF p = Nat.land (Nat.shiftRight (LF (p / 16)) (448 * (p % 16))) M448 := by
    change Nat.land (Nat.shiftRight (LF (Nat.shiftRight p 4)) (Nat.mul (Nat.land p 15) 448))
      M448 = _
    rw [e1, e2, nmul, mul_comm]
  rw [e3]
  exact orB_eq_true.1 h

theorem sumLt_succ (f : ℕ → ℕ) (n : ℕ) : sumLt (n + 1) f = sumLt n f + f n := by
  have e : sumLt (n + 1) f = strictN (sumLt n f) fun a => Nat.add a (f n) := rfl
  rw [e, CFSG.KC.TcRes.strictN_eq]
  rfl

theorem dg5_sumLt (a : ℕ → ℕ) (ha : ∀ i, a i < 5) :
    ∀ n, sumLt n (fun i => 5 ^ i * a i) < 5 ^ n ∧
      ∀ m < n, dg5 (sumLt n (fun i => 5 ^ i * a i)) m = a m := by
  have hdg : ∀ x m, dg5 x m = x / 5 ^ m % 5 := fun _ _ => rfl
  intro n
  induction n with
  | zero => exact ⟨Nat.one_pos, fun m hm => by omega⟩
  | succ n ih =>
    obtain ⟨hlt, hd⟩ := ih
    refine ⟨?_, fun m hm => ?_⟩
    · rw [sumLt_succ, pow_succ]
      have := ha n
      nlinarith [Nat.mul_le_mul_left (5 ^ n) (by omega : a n ≤ 4)]
    · rw [sumLt_succ, hdg]
      rcases Nat.lt_or_ge m n with h | h
      · have e : 5 ^ n * a n = 5 ^ m * (5 * (5 ^ (n - m - 1) * a n)) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_add]
          congr 2
          omega
        rw [e, Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num : 0 < 5)),
          Nat.add_mul_mod_self_left, ← hdg, hd m h]
      · have hmn : m = n := by omega
        subst hmn
        rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num : 0 < 5)),
          Nat.div_eq_of_lt hlt, zero_add, Nat.mod_eq_of_lt (ha m)]

theorem v5_lin5 (c1 c2 a : ℕ) : v5 (lin5 c1 c2 a) = (a : ZMod 5) • v5 c1 + v5 c2 := by
  funext m
  have e : lin5 c1 c2 a = sumLt 4 (fun i => 5 ^ i * ((a * dg5 c1 i + dg5 c2 i) % 5)) := rfl
  change (dg5 (lin5 c1 c2 a) m : ZMod 5) = (a : ZMod 5) * (dg5 c1 m : ZMod 5) + (dg5 c2 m : ZMod 5)
  rw [e, (dg5_sumLt _ (fun i => Nat.mod_lt _ (by norm_num)) 4).2 m m.2, ZMod.natCast_mod]
  push_cast
  ring

attribute [local instance] fact_prime_five_tcres in
theorem lines6 {P : Submodule (ZMod 5) (Fin 8 → ZMod 5)} {u1 u2 : Fin 8 → ZMod 5}
    (hind : ∀ s t : ZMod 5, s • u1 + t • u2 = 0 → s = 0 ∧ t = 0)
    (hP : ∀ v, v ∈ P ↔ ∃ s t : ZMod 5, v = s • u1 + t • u2) (xv : ℕ → Fin 8 → ZMod 5)
    (h0 : xv 0 = u1) (h1 : ∀ a < 5, xv (a + 1) = (a : ZMod 5) • u1 + u2) :
    (∀ y < 6, xv y ∈ P ∧ xv y ≠ 0) ∧
      ∀ v ∈ P, v ≠ 0 → ∃ y < 6, ∃ c : ZMod 5, c ≠ 0 ∧ v = c • xv y := by
  refine ⟨fun y hy => ?_, fun v hv hv0 => ?_⟩
  · rcases y with _ | a
    · refine ⟨(hP _).2 ⟨1, 0, by rw [h0]; simp⟩, fun h => ?_⟩
      rw [h0] at h
      exact one_ne_zero (hind 1 0 (by simp [h])).1
    · rw [h1 a (by omega)]
      refine ⟨(hP _).2 ⟨a, 1, by simp⟩, fun h => ?_⟩
      exact one_ne_zero (hind a 1 (by simpa using h)).2
  · obtain ⟨s, t, rfl⟩ := (hP v).1 hv
    by_cases ht : t = 0
    · subst ht
      have hs : s ≠ 0 := fun hs => hv0 (by simp [hs])
      exact ⟨0, by norm_num, s, hs, by simp [h0]⟩
    · refine ⟨(s / t).val + 1, by have := ZMod.val_lt (s / t); omega, t, ht, ?_⟩
      rw [h1 _ (ZMod.val_lt _), ZMod.natCast_zmod_val, smul_add, smul_smul, mul_div_cancel₀ _ ht]

theorem lam_inj {vec : ℕ → Fin Tag.E8.rank → ℤ} {T0 B PV MW r : ℕ}
    (hK : KerRaw vec T0 B PV MW r) : Function.Injective (lam B) := by
  have hpiv : ∀ (c : Fin 4 → ZMod 5) (k : Fin 4),
      lam B c (⟨fld PV 3 k % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = c k := by
    intro c k
    simp only [lam, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hK.piv, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  intro c d hcd
  funext k
  rw [← hpiv c k, ← hpiv d k]
  exact congrFun hcd _

theorem c2_ls_mid : ∀ l < 1010, C2M.LS (1038 + l) = 0 := by decide +kernel

theorem c2_ls_hi : ∀ l < 2048, C2M.LS (2048 + l) = C2M.LS l := by decide +kernel

theorem c2_hls : ∀ l < 4096, C2M.LS l = 0 ∨
    line8OK E8.ADJ C2M.POS C2M.DEC C2P.PW C2P.rcS C2P.bS (C2M.LS l) = true := by
  have low : ∀ l < 2048, C2M.LS l = 0 ∨
      line8OK E8.ADJ C2M.POS C2M.DEC C2P.PW C2P.rcS C2P.bS (C2M.LS l) = true := by
    intro l hl
    rcases Nat.lt_or_ge l 1038 with h | h
    · exact Or.inr (ch715750all.c2m_line l h)
    · left
      have := c2_ls_mid (l - 1038) (by omega)
      rwa [Nat.add_sub_cancel' h] at this
  intro l hl
  rcases Nat.lt_or_ge l 2048 with h | h
  · exact low l h
  · have := c2_ls_hi (l - 2048) (by omega)
    rw [Nat.add_sub_cancel' h] at this
    rw [this]
    exact low _ (by omega)

theorem c2p_lm : ∀ j < 4, C2P.lS j < 2 ^ (12 * 625) ∧ C2P.mS j < 2 ^ (12 * 625) := by
  decide +kernel

theorem vecMul_amat (vec : ℕ → Fin Tag.E8.rank → ℤ) (T0 r : ℕ) (v : Fin 8 → ZMod 5) (j : Fin 8) :
    Matrix.vecMul v (amat vec T0 r) j =
      ∑ m, v m * ((vec (fld T0 8 j) m : ℤ) : ZMod 5) - v j * (r : ZMod 5) := by
  simp only [Matrix.vecMul, dotProduct, amat, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem c2_phi0_surv {s : ℕ}
    (hs : s < 2) (ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ))
    (hiso : ∀ x y, iform (ψ x) (ψ y) = iform x y)
    (hroot : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (ψ γ))
    (hψ0 : ∀ m : Fin Tag.E8.rank,
      ψ (vecOf Tag.E8.rank E8.V m) = vecOf Tag.E8.rank E8.V (fld E8T.T0 8 m))
    {ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)} (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = ψ γ)
    {F f' : ℕ} (hf' : f' ∈ c2Flags s) (hflag : FlagTransfer 5 F f')
    (P : Submodule (ZMod 5) (Fin Tag.E8.rank → ZMod 5)) (hP2 : Module.finrank (ZMod 5) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 5) * v k = ((2 + s : ℕ) : ZMod 5) * v j)
    (iJ : KernelComponent (tcChiPl Tag.E8 5 P)) {x : Fin Tag.E8.rank → ZMod 5}
    (ix : KernelComponent (tcChiLn Tag.E8 5 x)) (hS : SurvHyp ρ F P iJ x ix) : False := by
  have hpw := pw8_spec e8D ch715750all.e8_root ch715751p.pw ψ hiso hψ0 t0_lt
  have hph : ∀ g < 240, vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g) =
      ψ (vecOf Tag.E8.rank E8.V g) := fun g hg => (hpw g hg).2
  have hphN : ∀ g < 240, fld C2P.PW 8 g < 240 := fun g hg => (hpw g hg).1
  have hphρ : ∀ g < 240, vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g) =
      ρ (vecOf Tag.E8.rank E8.V g) := fun g hg => (hph g hg).trans (hρ _ (e8D.isRoot g hg)).symm
  have hPK : ∀ v ∈ P, Matrix.vecMul v (amat (vecOf Tag.E8.rank E8.V) E8T.T0 (2 + s)) = 0 := by
    intro v hv
    funext j
    have hf := hfrob v hv j
    rw [hρ _ (IsRoot.basis (τ := Tag.E8) j), ← e8D.simple j, hψ0 j] at hf
    have hs' : ∑ m, v m * ((vecOf Tag.E8.rank E8.V (fld E8T.T0 8 j) m : ℤ) : ZMod 5) =
        ∑ k, ((vecOf Tag.E8.rank E8.V (fld E8T.T0 8 j) k : ℤ) : ZMod 5) * v k :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    refine (vecMul_amat _ _ _ v j).trans ?_
    change _ = (0 : ZMod 5)
    rw [sub_eq_zero]
    exact (hs'.trans hf).trans (mul_comm _ _)
  obtain ⟨B, PV, MW, hB, hK⟩ : ∃ B PV MW, C2P.bS s = B ∧
      KerRaw (vecOf Tag.E8.rank E8.V) E8T.T0 B PV MW (2 + s) := by
    interval_cases s
    · exact ⟨_, _, _, rfl, c2_ker0⟩
    · exact ⟨_, _, _, rfl, c2_ker1⟩
  have hsw5 := ch715750all.c2p_sw s hs
  obtain ⟨p, hap, hpe, hred, hspan⟩ :=
    exists_c2_record hK (sweep5Raw_of_checks ch715750all.c2p_tab c2p_lm hsw5) hP2 hPK
  have hbit := sw5_rec hsw5 p hap hpe
  have hpl := pl5_of_leaf ch715750all.c2p_leaf (p := p) (by omega)
  have hΦ : ∀ g, g ∈ PhiP5 (vecOf Tag.E8.rank E8.V)
      (lam B (v5 (Nat.land (prec5 C2P.LF p) 1023)))
      (lam B (v5 (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023))) ↔ g < 240 ∧
        ∀ v ∈ (P : Set (Fin Tag.E8.rank → ZMod 5)),
          ∑ m, v m * ((vecOf Tag.E8.rank E8.V g m : ℤ) : ZMod 5) = 0 := by
    intro g
    exact and_congr_right fun _ => (plane_cond hspan
      (fun m => ((vecOf Tag.E8.rank E8.V g m : ℤ) : ZMod 5))).symm
  have hmv01 : Nat.land (Nat.shiftRight (prec5 C2P.LF p) 21) 1 = 0 ∨
      Nat.land (Nat.shiftRight (prec5 C2P.LF p) 21) 1 = 1 := by
    have : Nat.land (Nat.shiftRight (prec5 C2P.LF p) 21) 1 < 2 := by
      rw [CFSG.KC.TcRes.Lane.nland]
      exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
    omega
  rcases hmv01 with hmv | hmv
  ·
    have hrec := pl5Rec_of_checks rfl e8D ch715750all.c2p_rc hpl hmv
    rw [hbit, hB] at hrec
    have h1 := orbitLength_one_of_rec e8D ψ ρ hρ hroot hiso ((2 + s : ℕ) : ZMod 5) P hfrob _ hΦ
      hph hrec iJ
    have h2 := hS.1
    omega
  ·
    have hana := (ml8_of_leaf ch715750all.c2m_leaf (p := p) (by omega)).resolve_left
      (by rw [hmv]; decide)
    have hblk := ana8Blocks_of_checks e8D (kmask5_lt ch715750all.c2p_rc _ _ _) hpl hana
    rw [hbit, hB] at hblk
    have hmk : mset 240 (kmask5 C2P.rcS B (Nat.land (prec5 C2P.LF p) 1023)
        (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023)) =
        PhiP5 (vecOf Tag.E8.rank E8.V) (lam B (v5 (Nat.land (prec5 C2P.LF p) 1023)))
          (lam B (v5 (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023))) :=
      mset_kmask5 ch715750all.c2p_rc _ _ _
    have himg := image_eq_kernelRoots e8D (P : Set (Fin Tag.E8.rank → ZMod 5)) _ hΦ
    rw [← hmk] at himg
    have hker := kernelRoots_frob_image ψ ρ hρ hroot ((2 + s : ℕ) : ZMod 5)
      (P : Set (Fin Tag.E8.rank → ZMod 5)) hfrob
    have hform : ∀ α ∈ kernelRoots (tcChiPl Tag.E8 5 P), ∀ β ∈ kernelRoots (tcChiPl Tag.E8 5 P),
        iform (ρ α) (ρ β) = iform α β := by
      intro α hα β hβ
      rw [hρ _ ((mem_kernelRoots_chiQ 5 _ α).1 hα).1, hρ _ ((mem_kernelRoots_chiQ 5 _ β).1 hβ).1,
        hiso]
    obtain ⟨γ0, hγ0⟩ : ∃ γ0, γ0 ∈ componentRoots (tcChiPl Tag.E8 5 P) iJ := by
      obtain ⟨y, rfl⟩ := Quotient.exists_rep iJ
      exact ⟨y.1, y.2, rfl⟩
    obtain ⟨g0, hg0, rfl⟩ : γ0 ∈ vecOf Tag.E8.rank E8.V '' mset 240
        (kmask5 C2P.rcS B (Nat.land (prec5 C2P.LF p) 1023)
          (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023)) := by
      rw [himg]
      exact hγ0.1
    obtain ⟨C, rt, hg0C, hrtC, hCΦ, hconn, hcl, -, holen⟩ := hblk g0 hg0
    obtain ⟨i, hi⟩ := exists_componentRoots_eq_image himg hCΦ hrtC hconn hcl
    have hiJ : i = iJ := eq_of_mem_componentRoots (hi ▸ Set.mem_image_of_mem _ hg0C) hγ0
    subst hiJ
    rcases holen with h1 | ⟨blk, hjb⟩
    · have hrN : rt < 240 := ((hCΦ hrtC : rt ∈ mset 240 _)).1
      have hin : fld C2P.PW 8 rt ∈ mset 240 C := ⟨hphN rt hrN, olen_one h1⟩
      have h1' : componentOrbitLength ρ (componentRoots (tcChiPl Tag.E8 5 P) i) = 1 := by
        refine componentOrbitLength_eq_of_first ρ hker hform i (γ := vecOf Tag.E8.rank E8.V rt)
          (by rw [hi]; exact Set.mem_image_of_mem _ hrtC) one_pos ?_ (fun s hs hs' => by omega)
        rw [Function.iterate_one, ← hphρ rt hrN, hi]
        exact Set.mem_image_of_mem _ hin
      have h2 := hS.1
      omega
    · have : Fact (Nat.Prime 5) := fact_prime_five_tcres
      obtain ⟨dJ, r0, hcJ, hks, -, E0, E1, E2, E3, E4, E5, hlines, hjok⟩ :=
        jb8OK_spec (V := E8.V) (X := E8.X) (Y := E8.Y) (QS := E8T.QS) (MVS := E8T.MVS)
          (RTs := E8.RTs) rfl e8D e8_hX ch715750all.t_q ch715750all.t_mv ch715750all.c2m_pos
          ch715750all.c2m_dec hphN
          (by
            rintro Φ' (rfl | ⟨s', x', rfl⟩)
            · exact sub_mem_kmask5 ch715750all.c2p_rc _ _ _
            · exact sub_mem_kv8 ch715750all.c2p_rc _ _)
          c2_hls
          (fun i hi m hm => (root_lanes (n := 8) (by norm_num) (ch715750all.e8_root i hi)).1 m hm)
          (fun g hg m => cart_row Tag.E8 e8_yc e8_ycb e8_ycl ch715750all.e8_root hg m)
          (fun g hg j => (root_lanes (n := 8) (by norm_num) (ch715750all.e8_root g hg)).2.2.1 j)
          e8_qb hjb
      obtain ⟨iJ', hiJ', hdJ⟩ := tcDataOK5_of_compRaw e8D ρ hker hform himg hphN hphρ hcJ hks
      have hiJ'' : iJ' = i := eq_of_mem_componentRoots
        (hiJ' ▸ Set.mem_image_of_mem _ hrtC) (hi ▸ Set.mem_image_of_mem _ hrtC)
      rw [hiJ''] at hdJ
      have hind : ∀ a b : ZMod 5, a • lam B (v5 (Nat.land (prec5 C2P.LF p) 1023)) +
          b • lam B (v5 (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023)) = 0 →
          a = 0 ∧ b = 0 := by
        intro a b h
        apply hred.indep
        apply lam_inj hK
        rw [lam_add, lam_smul, lam_smul, h]
        exact (map_zero (lamL B)).symm
      have hlin : ∀ a < 5, lam B (v5 (xs5 (Nat.land (prec5 C2P.LF p) 1023)
          (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023) (a + 1))) =
          (a : ZMod 5) • lam B (v5 (Nat.land (prec5 C2P.LF p) 1023)) +
            lam B (v5 (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023)) := by
        intro a ha
        have e : xs5 (Nat.land (prec5 C2P.LF p) 1023)
            (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023) (a + 1) =
            lin5 (Nat.land (prec5 C2P.LF p) 1023)
              (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023) a := by
          interval_cases a <;> rfl
        rw [e, v5_lin5, lam_add, lam_smul]
      obtain ⟨hxv, hcover⟩ := lines6 (P := P) hind hspan
        (fun y => lam B (v5 (xs5 (Nat.land (prec5 C2P.LF p) 1023)
          (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023) y))) rfl hlin
      have hmP : ∀ E, Nat.land (Nat.shiftRight (sel6 E0 E1 E2 E3 E4 E5 E) 35) M240 =
          sel6 (Nat.land (Nat.shiftRight E0 35) M240) (Nat.land (Nat.shiftRight E1 35) M240)
            (Nat.land (Nat.shiftRight E2 35) M240) (Nat.land (Nat.shiftRight E3 35) M240)
            (Nat.land (Nat.shiftRight E4 35) M240) (Nat.land (Nat.shiftRight E5 35) M240) E :=
        fun E => sel6_map (fun E => Nat.land (Nat.shiftRight E 35) M240) _ _ _ _ _ _ E
      have hmD : ∀ E, Nat.land (Nat.shiftRight (sel6 E0 E1 E2 E3 E4 E5 E) 11) 16777215 =
          sel6 (Nat.land (Nat.shiftRight E0 11) 16777215)
            (Nat.land (Nat.shiftRight E1 11) 16777215) (Nat.land (Nat.shiftRight E2 11) 16777215)
            (Nat.land (Nat.shiftRight E3 11) 16777215) (Nat.land (Nat.shiftRight E4 11) 16777215)
            (Nat.land (Nat.shiftRight E5 11) 16777215) E :=
        fun E => sel6_map (fun E => Nat.land (Nat.shiftRight E 11) 16777215) _ _ _ _ _ _ E
      have hmF : ∀ E, Nat.land (Nat.shiftRight (sel6 E0 E1 E2 E3 E4 E5 E) 275) 63 =
          sel6 (Nat.land (Nat.shiftRight E0 275) 63) (Nat.land (Nat.shiftRight E1 275) 63)
            (Nat.land (Nat.shiftRight E2 275) 63) (Nat.land (Nat.shiftRight E3 275) 63)
            (Nat.land (Nat.shiftRight E4 275) 63) (Nat.land (Nat.shiftRight E5 275) 63) E :=
        fun E => sel6_map (fun E => Nat.land (Nat.shiftRight E 275) 63) _ _ _ _ _ _ E
      have hlc : ∀ y < 6, ∃ iy : KernelComponent (tcChiLn Tag.E8 5
          (lam B (v5 (xs5 (Nat.land (prec5 C2P.LF p) 1023)
            (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023) y)))),
          componentRoots _ iy = vecOf Tag.E8.rank E8.V '' mset 240
            (sel6 (Nat.land (Nat.shiftRight E0 35) M240) (Nat.land (Nat.shiftRight E1 35) M240)
              (Nat.land (Nat.shiftRight E2 35) M240) (Nat.land (Nat.shiftRight E3 35) M240)
              (Nat.land (Nat.shiftRight E4 35) M240) (Nat.land (Nat.shiftRight E5 35) M240) y) ∧
          TcDataOK ρ (componentRoots _ iy) (tkCd5 (sel6 (Nat.land (Nat.shiftRight E0 11) 16777215)
            (Nat.land (Nat.shiftRight E1 11) 16777215) (Nat.land (Nat.shiftRight E2 11) 16777215)
            (Nat.land (Nat.shiftRight E3 11) 16777215) (Nat.land (Nat.shiftRight E4 11) 16777215)
            (Nat.land (Nat.shiftRight E5 11) 16777215) y)) := by
        intro y hy
        obtain ⟨-, -, ⟨g1, r1, hc1⟩, hks1, -⟩ := hlines y hy
        rw [hB] at hc1
        set x' := xs5 (Nat.land (prec5 C2P.LF p) 1023)
          (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023) y with hx'
        have hΦx : ∀ g, g ∈ mset 240 (kv8 C2P.rcS B x') ↔ g < 240 ∧
            ∀ v ∈ ({lam B (v5 x')} : Set (Fin Tag.E8.rank → ZMod 5)),
              ∑ m, v m * ((vecOf Tag.E8.rank E8.V g m : ℤ) : ZMod 5) = 0 := by
          intro g
          rw [mset_kv8 ch715750all.c2p_rc B x']
          exact and_congr_right fun _ => ⟨fun h v hv => by
            have hv' : v = lam B (v5 x') := hv
            rw [hv']
            exact h, fun h => h _ rfl⟩
        have himgx := image_eq_kernelRoots e8D
          ({lam B (v5 x')} : Set (Fin Tag.E8.rank → ZMod 5)) _ hΦx
        have hkerx := kernelRoots_frob_image ψ ρ hρ hroot ((2 + s : ℕ) : ZMod 5)
          ({lam B (v5 x')} : Set (Fin Tag.E8.rank → ZMod 5)) (fun v hv => by
            have hv' : v = lam B (v5 x') := hv
            rw [hv']
            exact hfrob _ (hxv y hy).1)
        have hformx : ∀ α ∈ kernelRoots (tcChiLn Tag.E8 5 (lam B (v5 x'))),
            ∀ β ∈ kernelRoots (tcChiLn Tag.E8 5 (lam B (v5 x'))),
              iform (ρ α) (ρ β) = iform α β := by
          intro α hα β hβ
          rw [hρ _ ((mem_kernelRoots_chiQ 5 _ α).1 hα).1,
            hρ _ ((mem_kernelRoots_chiQ 5 _ β).1 hβ).1, hiso]
        obtain ⟨iy, hiy, hdy⟩ := tcDataOK5_of_compRaw e8D ρ hkerx hformx himgx hphN hphρ hc1 hks1
        refine ⟨iy, ?_, ?_⟩
        · rw [hmP] at hiy
          exact hiy
        · rw [← hmD]
          exact hdy
      choose ix' hix' hdx' using hlc
      obtain ⟨y, hy, hΨy, hΨne, hspl, hrest⟩ := surv_lines hflag P i hdJ
        (γ0 := vecOf Tag.E8.rank E8.V rt) (by rw [hi]; exact Set.mem_image_of_mem _ hrtC)
        (n := 6) (fun y => lam B (v5 (xs5 (Nat.land (prec5 C2P.LF p) 1023)
          (Nat.land (Nat.shiftRight (prec5 C2P.LF p) 10) 1023) y))) hxv hcover
        (fun y => vecOf Tag.E8.rank E8.V '' mset 240
          (sel6 (Nat.land (Nat.shiftRight E0 35) M240) (Nat.land (Nat.shiftRight E1 35) M240)
            (Nat.land (Nat.shiftRight E2 35) M240) (Nat.land (Nat.shiftRight E3 35) M240)
            (Nat.land (Nat.shiftRight E4 35) M240) (Nat.land (Nat.shiftRight E5 35) M240) y))
        (fun y => tkCd5 (sel6 (Nat.land (Nat.shiftRight E0 11) 16777215)
          (Nat.land (Nat.shiftRight E1 11) 16777215) (Nat.land (Nat.shiftRight E2 11) 16777215)
          (Nat.land (Nat.shiftRight E3 11) 16777215) (Nat.land (Nat.shiftRight E4 11) 16777215)
          (Nat.land (Nat.shiftRight E5 11) 16777215) y))
        (fun y hy => ⟨ix' y hy, (hix' y hy).symm⟩)
        (fun y hy => by
          have := (hlines y hy).g0_mem
          rw [hmP] at this
          exact Set.mem_image_of_mem _ this)
        (fun y hy => by rw [← hix' y hy]; exact hdx' y hy)
        hS.2.1 hS.2.2.1 ix hS.2.2.2.1 hS.2.2.2.2.1 hS.2.2.2.2.2.1 hS.2.2.2.2.2.2
      have hps : sel6 (Nat.land (Nat.shiftRight E0 35) M240) (Nat.land (Nat.shiftRight E1 35) M240)
          (Nat.land (Nat.shiftRight E2 35) M240) (Nat.land (Nat.shiftRight E3 35) M240)
          (Nat.land (Nat.shiftRight E4 35) M240) (Nat.land (Nat.shiftRight E5 35) M240) y ≠ C := by
        intro h
        apply hΨne
        simp only [h, hi]
      have hfs : ∀ y < 6, sel6 (Nat.land (Nat.shiftRight E0 275) 63)
          (Nat.land (Nat.shiftRight E1 275) 63) (Nat.land (Nat.shiftRight E2 275) 63)
          (Nat.land (Nat.shiftRight E3 275) 63) (Nat.land (Nat.shiftRight E4 275) 63)
          (Nat.land (Nat.shiftRight E5 275) 63) y =
          flags5 (sel6 (Nat.land (Nat.shiftRight E0 11) 16777215)
            (Nat.land (Nat.shiftRight E1 11) 16777215) (Nat.land (Nat.shiftRight E2 11) 16777215)
            (Nat.land (Nat.shiftRight E3 11) 16777215) (Nat.land (Nat.shiftRight E4 11) 16777215)
            (Nat.land (Nat.shiftRight E5 11) 16777215) y) := by
        intro y hy
        rw [← hmF, ← hmD]
        exact (hlines y hy).flags
      exact jok5_spec hfs hjok f' hf' y hy hps hspl hrest

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes in
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit) in
open CFSG.StandardType (GGLabelIso) in
theorem certificate715751_of_checks :
 ∀ (φ : AddMonoid.End (Fin Tag.E8.rank → ℤ)), (∀ x y, iform (φ x) (φ y) = iform x y) →
    (∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (φ γ)) → (∀ x, φ (φ x) = -x) →
    ∀ (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)), (∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ) →
    ∀ {F r : ℕ}, ((r = 2 ∧ (F = 1 ∨ (F % 4 = 1 ∧ 5 ≤ F))) ∨ (r = 3 ∧ F % 4 = 3 ∧ 3 ≤ F)) →
    ∀ (P : Submodule (ZMod 5) (Fin Tag.E8.rank → ZMod 5)), Module.finrank (ZMod 5) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod 5) * v k = (r : ZMod 5) * v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E8 5 P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E8 5 P) iJ) →
    ∀ {x : Fin Tag.E8.rank → ZMod 5}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E8 5 x)),
    componentRoots (tcChiPl Tag.E8 5 P) iJ ⊆ componentRoots (tcChiLn Tag.E8 5 x) ix →
    componentRoots (tcChiLn Tag.E8 5 x) ix ≠ componentRoots (tcChiPl Tag.E8 5 P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 5 x) ix)) ∧
      LargeEvenSplit 5 lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod 5, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E8 5 d),
      componentRoots (tcChiPl Tag.E8 5 P) iJ ⊆ componentRoots (tcChiLn Tag.E8 5 d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E8 5 d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E8 5 P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 5 d) i)) ∧
        LargeEvenHalfSplit 5 lab' c) → False := by
  intro φ hiso hroot hsq ρ hρ F r hfl P hP2 hfrob iJ hJ2 x hxP hx0 ix hJx hne hsplit hoth
  have hS : SurvHyp ρ F P iJ x ix := ⟨hJ2, hxP, hx0, hJx, hne, hsplit, hoth⟩
  obtain ⟨h, hh⟩ := exists_conj_phi0 e8D c2_search (t0_lt 0 (by norm_num)) e8_beta0 φ hiso hsq
    hroot
  let ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ) := tcrWEnd Tag.E8 h * φ * tcrWEnd Tag.E8 h⁻¹
  have hψ : ∀ y, ψ y = h • φ (h⁻¹ • y) := fun _ => rfl
  have hρ' : ∀ γ, IsRoot Tag.E8 γ → tcrConjPerm h ρ γ = ψ γ := tcrConjPerm_root h φ ρ hρ
  have hiso' : ∀ a b, iform (ψ a) (ψ b) = iform a b := by
    intro a b
    rw [hψ, hψ, iform_smul, hiso, iform_smul]
  have hroot' : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (ψ γ) := fun γ hγ => by
    rw [hψ]
    exact IsRoot.smul (hroot _ (IsRoot.smul hγ h⁻¹)) h
  obtain ⟨iJ', ix', -, -, hS'⟩ := SurvHyp.conj h hS
  have hfrob' := tcrDual_frob h φ ρ hρ (r : ZMod 5) P hfrob
  have hP2' : Module.finrank (ZMod 5) (P.map (tcrDualLin h 5)) = 2 := by
    rw [finrank_map_tcrDualLin]
    exact hP2
  rcases hfl with ⟨rfl, hF⟩ | ⟨rfl, h4, h3⟩
  · have hfl' : FlagTransfer 5 F (if F = 1 then 1 else 5) := by
      rcases hF with rfl | ⟨h4, h5⟩
      · simpa using flagTransfer_refl 5 1
      · rw [if_neg (by omega)]
        exact flagTransfer_five (by omega) (by norm_num) (by omega) (by omega) (by norm_num)
    exact c2_phi0_surv (s := 0) (by norm_num) ψ hiso' hroot' hh hρ'
      (by rw [show c2Flags 0 = [1, 5] from rfl]; split_ifs <;> simp) hfl' _ hP2'
      (fun v hv j => by simpa using hfrob' v hv j) iJ' ix' hS'
  · exact c2_phi0_surv (s := 1) (by norm_num) ψ hiso' hroot' hh hρ' (f' := 3) (by decide)
      (flagTransfer_five (by omega) (by norm_num) (by omega) h3 (by norm_num)) _ hP2'
      (fun v hv j => by simpa using hfrob' v hv j) iJ' ix' hS'

@[expose] def C3NoSurv (a b : ℕ) : Prop :=
  ∀ {p : ℕ} [Fact p.Prime], 13 ≤ p → ∀ {F : ℕ}, orderOf ((2 : ZMod p) ^ F) = 4 →
    ∀ (φ : AddMonoid.End (Fin Tag.E8.rank → ℤ)) (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)),
    (∀ x y, iform (φ x) (φ y) = iform x y) → (∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ) →
    (∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g)) →
    ∀ P : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p), Module.finrank (ZMod p) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j) →
    ∀ iJ : KernelComponent (tcChiPl Tag.E8 p P),
    vecOf Tag.E8.rank E8.V a ∈ componentRoots (tcChiPl Tag.E8 p P) iJ →
    vecOf Tag.E8.rank E8.V b ∈ componentRoots (tcChiPl Tag.E8 p P) iJ →
    ∀ (x : Fin Tag.E8.rank → ZMod p) (ix : KernelComponent (tcChiLn Tag.E8 p x)),
    SurvHyp ρ F P iJ x ix → False

theorem c3_gen {k : ℕ} (hk : k < 3) :
    ∃ ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ), (∀ x y, iform (ψ x) (ψ y) = iform x y) ∧
      (∀ g < 240, fld (C3.PGs k) 8 g < 240 ∧
        vecOf Tag.E8.rank E8.V (fld (C3.PGs k) 8 g) = ψ (vecOf Tag.E8.rank E8.V g)) ∧
      ∀ g < 240, fld (C3.PGs k) 8 (fld C2P.PW 8 g) = fld C2P.PW 8 (fld (C3.PGs k) 8 g) :=
  gen_spec e8D ch715750all.e8_root e8_hX (ch715750all.c3_gen k hk)

theorem c3_hPG :
    ∀ k < 3, ∀ g < 240, fld (C3.PGs k) 8 g < 240 := fun _ hk g hg => by
  obtain ⟨_, _, h, _⟩ := c3_gen hk
  exact (h g hg).1

@[expose] noncomputable def lw (RTs : ℕ → ℕ) (wl : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ x => x)
    (fun _ ih w x => ih (Nat.shiftRight w 3) (fld (RTs (Nat.land w 7)) 8 x)) wl

theorem weyl_of_lw :
    ∀ wl w (f : ℕ → ℕ), (∀ m < 8, f m < 240) → (∀ m < 8, lw E8.RTs wl w (f m) = m) →
      ∃ h : WeylGroup Tag.E8, ∀ m : Fin Tag.E8.rank,
        h • vecOf Tag.E8.rank E8.V m = vecOf Tag.E8.rank E8.V (f m) := by
  intro wl
  induction wl with
  | zero =>
    intro w f _ hw
    refine ⟨1, fun m => ?_⟩
    rw [one_smul]
    have hfm : f m = m := hw m m.2
    rw [hfm]
  | succ wl ih =>
    intro w f hf hw
    have hstep : ∀ m < 8, lw E8.RTs wl (w >>> 3) (fld (E8.RTs (w &&& 7)) 8 (f m)) = m :=
      fun m hm => hw m hm
    have hl : w &&& 7 < 8 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
    set l := w &&& 7 with hldef
    let s : WeylGroup Tag.E8 := simple Tag.E8 ⟨l, hl⟩
    have hvl : vecOf Tag.E8.rank E8.V l = Pi.single (⟨l, hl⟩ : Fin Tag.E8.rank) 1 :=
      e8D.simple ⟨l, hl⟩
    have hs : ∀ v : Fin Tag.E8.rank → ℤ,
        s • v = v - iform v (vecOf Tag.E8.rank E8.V l) • vecOf Tag.E8.rank E8.V l := by
      intro v
      change simple Tag.E8 ⟨l, hl⟩ • v = _
      rw [simple_smul, hvl, iform_single Tag.E8 e8_sym]
      rfl
    have hll : iform (vecOf Tag.E8.rank E8.V l) (vecOf Tag.E8.rank E8.V l) = 2 :=
      iform_root_self e8D (by omega)
    have hss : ∀ v : Fin Tag.E8.rank → ℤ, s • s • v = v := by
      intro v
      rw [hs v, hs (v - iform v (vecOf Tag.E8.rank E8.V l) • vecOf Tag.E8.rank E8.V l),
        iform_sub_left, iform_smul_left, hll]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hf' : ∀ m < 8, fld (E8.RTs l) 8 (f m) < 240 ∧
        vecOf Tag.E8.rank E8.V (fld (E8.RTs l) 8 (f m)) = s • vecOf Tag.E8.rank E8.V (f m) := by
      intro m hm
      obtain ⟨r1, hr1⟩ := e8D.refl l (by omega) (f m) (hf m hm)
      exact ⟨r1, by rw [hr1, hs]⟩
    obtain ⟨h', hh'⟩ := ih (w >>> 3) (fun m => fld (E8.RTs l) 8 (f m))
      (fun m hm => (hf' m hm).1) hstep
    refine ⟨s * h', fun m => ?_⟩
    rw [mul_smul, hh' m]
    beta_reduce
    rw [(hf' m m.2).2, hss]

theorem weyl_eq_end
    {h : WeylGroup Tag.E8} {ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ)}
    (hm : ∀ m : Fin Tag.E8.rank, h • vecOf Tag.E8.rank E8.V m = ψ (vecOf Tag.E8.rank E8.V m))
    (x : Fin Tag.E8.rank → ℤ) : h • x = ψ x := by
  have hx : x = ∑ m, x m • vecOf Tag.E8.rank E8.V m := by
    funext k
    simp only [e8D.simple, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e : h • x = tcrWEnd Tag.E8 h x := rfl
  rw [e, hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_zsmul, map_zsmul]
  exact congrArg _ (hm m)

@[expose] def c3WL (k : ℕ) : ℕ := if k = 0 then 14 else 24

@[expose] def c3W (k : ℕ) : ℕ :=
  if k = 0 then 1974588717195 else if k = 1 then 180701509057864317080
  else 4090908385842912469728

theorem c3_word : ∀ k < 3, ∀ m < 8, lw E8.RTs (c3WL k) (c3W k) (fld (C3.PGs k) 8 m) = m := by
  decide +kernel

theorem pw_lt : ∀ g < 240, fld C2P.PW 8 g < 240 := by decide +kernel

theorem c3_gen_weyl {k : ℕ}
    (hk : k < 3) : ∃ h : WeylGroup Tag.E8, ∀ g < 240, fld (C3.PGs k) 8 g < 240 ∧
      h • vecOf Tag.E8.rank E8.V g = vecOf Tag.E8.rank E8.V (fld (C3.PGs k) 8 g) := by
  obtain ⟨ψ, -, hψ, -⟩ := c3_gen hk
  obtain ⟨h, hh⟩ := weyl_of_lw (c3WL k) (c3W k) (fun m => fld (C3.PGs k) 8 m)
    (fun m hm => (hψ m (by omega)).1) (fun m hm => c3_word k hk m hm)
  have hm : ∀ m : Fin Tag.E8.rank, h • vecOf Tag.E8.rank E8.V m = ψ (vecOf Tag.E8.rank E8.V m) :=
    fun m => (hh m).trans (hψ m (m.2.trans_le (by decide))).2
  refine ⟨h, fun g hg => ⟨(hψ g hg).1, ?_⟩⟩
  rw [weyl_eq_end hm, (hψ g hg).2]

theorem c3NoSurv_gen {k : ℕ}
    (hk : k < 3) {a b : ℕ} (ha : a < 240) (hb : b < 240) (h : C3NoSurv a b) :
    C3NoSurv (fld (C3.PGs k) 8 a) (fld (C3.PGs k) 8 b) := by
  intro p _ hp13 F hF4 φ ρ hiso hρ hφ P hP2 hfrob iJ ha' hb' x ix hS
  obtain ⟨u, hu⟩ := c3_gen_weyl hk
  obtain ⟨-, -, -, hc⟩ := c3_gen hk
  obtain ⟨iJ', ix', hiJ', -, hS'⟩ := SurvHyp.conj u⁻¹ hS
  have hfrob' := tcrDual_frob u⁻¹ φ ρ hρ (((2 ^ F : ℕ) : ZMod p)) P hfrob
  have hP2' : Module.finrank (ZMod p) (P.map (tcrDualLin u⁻¹ p)) = 2 := by
    rw [finrank_map_tcrDualLin]
    exact hP2
  let φ' : AddMonoid.End (Fin Tag.E8.rank → ℤ) := tcrWEnd Tag.E8 u⁻¹ * φ * tcrWEnd Tag.E8 u⁻¹⁻¹
  have hρ' : ∀ γ, IsRoot Tag.E8 γ → tcrConjPerm u⁻¹ ρ γ = φ' γ := tcrConjPerm_root u⁻¹ φ ρ hρ
  have hφ' : ∀ g < 240, φ' (vecOf Tag.E8.rank E8.V g) =
      vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g) := by
    intro g hg
    change u⁻¹ • φ (u⁻¹⁻¹ • vecOf Tag.E8.rank E8.V g) = _
    rw [inv_inv, (hu g hg).2, hφ _ (hu g hg).1, ← hc g hg, ← (hu _ (pw_lt g hg)).2,
      inv_smul_smul]
  have haJ : vecOf Tag.E8.rank E8.V a ∈
      componentRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin u⁻¹ p))) iJ' := by
    rw [hiJ']
    exact ⟨_, ha', by rw [← (hu a ha).2]; exact inv_smul_smul u _⟩
  have hbJ : vecOf Tag.E8.rank E8.V b ∈
      componentRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin u⁻¹ p))) iJ' := by
    rw [hiJ']
    exact ⟨_, hb', by rw [← (hu b hb).2]; exact inv_smul_smul u _⟩
  have hiso' : ∀ x y, iform (φ' x) (φ' y) = iform x y := by
    intro x y
    change iform (u⁻¹ • φ (u⁻¹⁻¹ • x)) (u⁻¹ • φ (u⁻¹⁻¹ • y)) = _
    rw [iform_smul, hiso, iform_smul]
  unfold C3NoSurv at h
  exact h (p := p) hp13 hF4 φ' (tcrConjPerm u⁻¹ ρ) hiso' hρ' hφ' _ hP2' hfrob' iJ' haJ hbJ _ ix'
    hS'

theorem c3NoSurv_wapp {a b : ℕ}
    (ha : a < 240) (hb : b < 240) (h : C3NoSurv a b) :
    ∀ ks : List ℕ, (∀ k ∈ ks, k < 3) → C3NoSurv (wapp C3.PGs ks a) (wapp C3.PGs ks b)
  | [], _ => h
  | k :: ks, hks => by
    have hk := hks k (by simp)
    have hks' : ∀ k' ∈ ks, k' < 3 := fun k' hk' => hks k' (by simp [hk'])
    exact c3NoSurv_gen hk (wapp_lt c3_hPG ha ks hks') (wapp_lt c3_hPG hb ks hks')
      (c3NoSurv_wapp ha hb h ks hks')

theorem c3_lincomb {V COLS XM : ℕ} {d : ℤ}
    (hBX : ∀ i < 8, ∀ j < 8, ∑ k ∈ Finset.range 8, ((fld (fld V 128 (fld COLS 8 k)) 16 i : ℤ) - 7) *
        ((fld XM 8 (8 * k + j) : ℤ) - 128) = if i = j then d else 0)
    (e : ℕ) {m : ℕ} (hm : m < 8) :
    d * ((fld (fld V 128 e) 16 m : ℤ) - 7) =
      ∑ i ∈ Finset.range 8, ((fld (fld V 128 (fld COLS 8 i)) 16 m : ℤ) - 7) * Yv V XM e i := by
  have h1 : d * ((fld (fld V 128 e) 16 m : ℤ) - 7) = ∑ j ∈ Finset.range 8,
      (if m = j then d else 0) * ((fld (fld V 128 e) 16 j : ℤ) - 7) := by
    rw [Finset.sum_eq_single m (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_mul])
      (fun h => absurd (Finset.mem_range.2 hm) h), if_pos rfl]
  rw [h1]
  have h2 : ∀ j ∈ Finset.range 8, (if m = j then d else 0) * ((fld (fld V 128 e) 16 j : ℤ) - 7) =
      ∑ k ∈ Finset.range 8, ((fld (fld V 128 (fld COLS 8 k)) 16 m : ℤ) - 7) *
        (((fld XM 8 (8 * k + j) : ℤ) - 128) * ((fld (fld V 128 e) 16 j : ℤ) - 7)) := by
    intro j hj
    rw [← hBX m hm j (Finset.mem_range.1 hj), Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  rfl

theorem c3_coord {V COLS XM : ℕ} {d : ℤ}
    (hBX : ∀ i < 8, ∀ j < 8, ∑ k ∈ Finset.range 8, ((fld (fld V 128 (fld COLS 8 k)) 16 i : ℤ) - 7) *
        ((fld XM 8 (8 * k + j) : ℤ) - 128) = if i = j then d else 0)
    {p : ℕ} (u : Fin Tag.E8.rank → ZMod p) (e : ℕ) :
    (d : ZMod p) * ∑ m, u m * ((vecOf Tag.E8.rank V e m : ℤ) : ZMod p) =
      ∑ i ∈ Finset.range 8, ((Yv V XM e i : ℤ) : ZMod p) *
        ∑ m, u m * ((vecOf Tag.E8.rank V (fld COLS 8 i) m : ℤ) : ZMod p) := by
  have hm : ∀ m : Fin Tag.E8.rank, (d : ZMod p) * (u m * ((vecOf Tag.E8.rank V e m : ℤ) : ZMod p)) =
      ∑ i ∈ Finset.range 8, ((Yv V XM e i : ℤ) : ZMod p) *
        (u m * ((vecOf Tag.E8.rank V (fld COLS 8 i) m : ℤ) : ZMod p)) := by
    intro m
    have h := congrArg (fun z : ℤ => (z : ZMod p)) (c3_lincomb hBX e (m := m) m.2)
    simp only [Int.cast_mul, Int.cast_sum] at h
    have h' : (d : ZMod p) * ((vecOf Tag.E8.rank V e m : ℤ) : ZMod p) =
        ∑ i ∈ Finset.range 8, ((vecOf Tag.E8.rank V (fld COLS 8 i) m : ℤ) : ZMod p) *
          ((Yv V XM e i : ℤ) : ZMod p) := h
    calc (d : ZMod p) * (u m * ((vecOf Tag.E8.rank V e m : ℤ) : ZMod p))
        = u m * ((d : ZMod p) * ((vecOf Tag.E8.rank V e m : ℤ) : ZMod p)) := by ring
      _ = _ := by
        rw [h', Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun m _ => hm m, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

@[expose] noncomputable def c3pr {p : ℕ} (g : ℕ) (u : Fin Tag.E8.rank → ZMod p) : ZMod p :=
  ∑ k, ((vecOf Tag.E8.rank E8.V g k : ℤ) : ZMod p) * u k

@[expose] noncomputable def c3d : ℤ := (C3.DD : ℤ) - 128

@[expose] noncomputable def c3A {p : ℕ} (r : ZMod p) (e : ℕ) : ZMod p :=
  ((Yv E8.V C3.XM e 4 : ℤ) : ZMod p) + r * ((Yv E8.V C3.XM e 5 : ℤ) : ZMod p)

@[expose] noncomputable def c3B {p : ℕ} (r : ZMod p) (e : ℕ) : ZMod p :=
  ((Yv E8.V C3.XM e 6 : ℤ) : ZMod p) + r * ((Yv E8.V C3.XM e 7 : ℤ) : ZMod p)

theorem c3_bx : c3d ≠ 0 ∧ c3d.natAbs ∣ 30 ^ 64 ∧ ∀ i < 8, ∀ j < 8,
    ∑ k ∈ Finset.range 8, ((fld (fld E8.V 128 (fld C3.COLS 8 k)) 16 i : ℤ) - 7) *
      ((fld C3.XM 8 (8 * k + j) : ℤ) - 128) = if i = j then c3d else 0 :=
  bx_spec (fun k hk m hm => (root_lanes (n := 8) (by norm_num)
    (ch715750all.e8_root _ ((cols_spec ch715752.cols).1 k hk))).1 m hm) ch715752.bx

theorem c3_unit {p : ℕ} [hp : Fact p.Prime] (h7 : 7 ≤ p) {n : ℤ} (h0 : n ≠ 0)
    (hs : n.natAbs ∣ 30 ^ 64) : (n : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h1 : p ∣ n.natAbs := Int.natCast_dvd.1 h
  have h2 : p ∣ 2 * 3 * 5 := hp.out.dvd_of_dvd_pow (h1.trans hs)
  rcases (Nat.Prime.dvd_mul hp.out).1 h2 with h3 | h3
  · rcases (Nat.Prime.dvd_mul hp.out).1 h3 with h4 | h4
    · have := Nat.le_of_dvd (by norm_num) h4
      omega
    · have := Nat.le_of_dvd (by norm_num) h4
      omega
  · have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem c3_coord' {p : ℕ} (u : Fin Tag.E8.rank → ZMod p) (e : ℕ) :
    (c3d : ZMod p) * c3pr e u = ∑ i ∈ Finset.range 8, ((Yv E8.V C3.XM e i : ℤ) : ZMod p) *
      c3pr (fld C3.COLS 8 i) u := by
  have h := c3_coord c3_bx.2.2 u e
  have e1 : ∀ g, c3pr g u = ∑ m, u m * ((vecOf Tag.E8.rank E8.V g m : ℤ) : ZMod p) :=
    fun g => Finset.sum_congr rfl fun m _ => mul_comm _ _
  rw [e1]
  simp only [e1]
  exact h

section C3Plane

variable {p : ℕ} [Fact p.Prime] {F : ℕ} {φ : AddMonoid.End (Fin Tag.E8.rank → ℤ)}
  {ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)} {P : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p)}

theorem c3_formula
    (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    (hφ : ∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g))
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    (h0 : ∀ u ∈ P, c3pr (fld C3.COLS 8 0) u = 0) (h2 : ∀ u ∈ P, c3pr (fld C3.COLS 8 2) u = 0)
    {u : Fin Tag.E8.rank → ZMod p} (hu : u ∈ P) (e : ℕ) :
    (c3d : ZMod p) * c3pr e u = c3A ((2 ^ F : ℕ) : ZMod p) e * c3pr (fld C3.COLS 8 4) u +
      c3B ((2 ^ F : ℕ) : ZMod p) e * c3pr (fld C3.COLS 8 6) u := by
  obtain ⟨hcl, hcp⟩ := cols_spec ch715752.cols
  have hodd : ∀ i < 4, c3pr (fld C3.COLS 8 (2 * i + 1)) u =
      ((2 ^ F : ℕ) : ZMod p) * c3pr (fld C3.COLS 8 (2 * i)) u := by
    intro i hi
    have hc := hcl (2 * i) (by omega)
    have hr := e8D.isRoot _ hc
    rw [hcp i hi]
    unfold c3pr
    rw [← hφ _ hc, ← hρ _ hr]
    exact tch_frob_root φ ρ hρ _ u (hfrob u hu) _ hr
  have hs1 : c3pr (fld C3.COLS 8 1) u = ((2 ^ F : ℕ) : ZMod p) * c3pr (fld C3.COLS 8 0) u :=
    hodd 0 (by norm_num)
  have hs3 : c3pr (fld C3.COLS 8 3) u = ((2 ^ F : ℕ) : ZMod p) * c3pr (fld C3.COLS 8 2) u :=
    hodd 1 (by norm_num)
  have hs5 : c3pr (fld C3.COLS 8 5) u = ((2 ^ F : ℕ) : ZMod p) * c3pr (fld C3.COLS 8 4) u :=
    hodd 2 (by norm_num)
  have hs7 : c3pr (fld C3.COLS 8 7) u = ((2 ^ F : ℕ) : ZMod p) * c3pr (fld C3.COLS 8 6) u :=
    hodd 3 (by norm_num)
  rw [c3_coord' u e]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hs1, hs3, hs5, hs7, h0 u hu, h2 u hu]
  unfold c3A c3B
  ring

theorem c3_inj (hp : 13 ≤ p)
    (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    (hφ : ∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g))
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    (h0 : ∀ u ∈ P, c3pr (fld C3.COLS 8 0) u = 0) (h2 : ∀ u ∈ P, c3pr (fld C3.COLS 8 2) u = 0)
    {u : Fin Tag.E8.rank → ZMod p} (hu : u ∈ P) (h4 : c3pr (fld C3.COLS 8 4) u = 0)
    (h6 : c3pr (fld C3.COLS 8 6) u = 0) : u = 0 := by
  have hd := c3_unit (p := p) (by omega) c3_bx.1 c3_bx.2.1
  funext m
  have hf := c3_formula hρ hφ hfrob h0 h2 hu m
  rw [h4, h6, mul_zero, mul_zero, add_zero] at hf
  have hm : c3pr m u = 0 := (mul_eq_zero.1 hf).resolve_left hd
  unfold c3pr at hm
  rw [e8D.simple m] at hm
  simpa [Pi.single_apply] using hm

@[expose] noncomputable def c3S (P : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p)) :
    P →ₗ[ZMod p] ZMod p × ZMod p where
  toFun u := (c3pr (fld C3.COLS 8 4) (u : Fin Tag.E8.rank → ZMod p),
    c3pr (fld C3.COLS 8 6) (u : Fin Tag.E8.rank → ZMod p))
  map_add' a b := by
    simp only [c3pr, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib,
      Prod.mk_add_mk]
  map_smul' c a := by
    simp only [c3pr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      RingHom.id_apply, Prod.smul_mk]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> exact Finset.sum_congr rfl fun _ _ => by ring

theorem c3_surj (hp : 13 ≤ p)
    (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    (hφ : ∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g))
    (hP2 : Module.finrank (ZMod p) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    (h0 : ∀ u ∈ P, c3pr (fld C3.COLS 8 0) u = 0) (h2 : ∀ u ∈ P, c3pr (fld C3.COLS 8 2) u = 0)
    (s t : ZMod p) : ∃ u ∈ P, c3pr (fld C3.COLS 8 4) u = s ∧ c3pr (fld C3.COLS 8 6) u = t := by
  have hinj : Function.Injective (c3S P) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h4 : c3pr (fld C3.COLS 8 4) (u : Fin Tag.E8.rank → ZMod p) = 0 := congrArg Prod.fst hu
    have h6 : c3pr (fld C3.COLS 8 6) (u : Fin Tag.E8.rank → ZMod p) = 0 := congrArg Prod.snd hu
    exact Subtype.ext (c3_inj hp hρ hφ hfrob h0 h2 u.2 h4 h6)
  have hdim : Module.finrank (ZMod p) P = Module.finrank (ZMod p) (ZMod p × ZMod p) := by
    rw [hP2, Module.finrank_prod, Module.finrank_self]
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj (s, t)
  exact ⟨u, u.2, congrArg Prod.fst hu, congrArg Prod.snd hu⟩

theorem c3_r_sq (hF4 : orderOf ((2 : ZMod p) ^ F) = 4) :
    ((2 ^ F : ℕ) : ZMod p) * ((2 ^ F : ℕ) : ZMod p) = -1 := by
  have hq : ((2 ^ F : ℕ) : ZMod p) = (2 : ZMod p) ^ F := by push_cast; rfl
  rw [hq]
  set q : ZMod p := (2 : ZMod p) ^ F with hqdef
  have h4 : q ^ 4 = 1 := by rw [← hF4]; exact pow_orderOf_eq_one q
  have h2 : q ^ 2 ≠ 1 := by
    intro h
    have : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hF4] at this
    omega
  have h5 : (q ^ 2 - 1) * (q ^ 2 + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.1 h5 with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · linear_combination h

theorem c3_gauss_ne (h7 : 7 ≤ p) {r : ZMod p} (hr : r * r = -1) {x y : ℤ}
    (h0 : ¬ (x = 0 ∧ y = 0)) (hs : (x ^ 2 + y ^ 2).natAbs ∣ 30 ^ 64) :
    (x : ZMod p) + r * (y : ZMod p) ≠ 0 := by
  intro h
  have hn : x ^ 2 + y ^ 2 ≠ 0 := by
    intro hz
    apply h0
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  apply c3_unit h7 hn hs
  have e : ((x ^ 2 + y ^ 2 : ℤ) : ZMod p) =
      ((x : ZMod p) + r * (y : ZMod p)) * ((x : ZMod p) - r * (y : ZMod p)) := by
    push_cast
    linear_combination ((y : ZMod p) ^ 2) * hr
  rw [e, h, zero_mul]

theorem c3_ker_iff (hp : 13 ≤ p)
    (hF4 : orderOf ((2 : ZMod p) ^ F) = 4)
    (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    (hφ : ∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g))
    (hP2 : Module.finrank (ZMod p) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    (h0 : ∀ u ∈ P, c3pr (fld C3.COLS 8 0) u = 0) (h2 : ∀ u ∈ P, c3pr (fld C3.COLS 8 2) u = 0)
    {e : ℕ} (he : e < 240) : (∀ u ∈ P, c3pr e u = 0) ↔ C3.SG.testBit e = true := by
  have hVl : ∀ g < 240, ∀ m < 8, fld (fld E8.V 128 g) 16 m < 16 := fun g hg =>
    (root_lanes (n := 8) (by norm_num) (ch715750all.e8_root g hg)).1
  have hpb := pbE_spec hVl he (pbW_spec ch715750all.c3_root e he)
  have hd := c3_unit (p := p) (by omega) c3_bx.1 c3_bx.2.1
  have hr := c3_r_sq hF4
  constructor
  · intro hk
    by_contra hn
    rw [Bool.not_eq_true] at hn
    rcases (hpb.2 hn).1 with ⟨hz, hs⟩ | ⟨hz, hs⟩
    · obtain ⟨u, hu, h4, h6⟩ := c3_surj hp hρ hφ hP2 hfrob h0 h2 1 0
      have hf := c3_formula hρ hφ hfrob h0 h2 hu e
      rw [hk u hu, h4, h6, mul_zero, mul_one, mul_zero, add_zero] at hf
      exact c3_gauss_ne (by omega) hr hz hs (by unfold c3A at hf; exact hf.symm)
    · obtain ⟨u, hu, h4, h6⟩ := c3_surj hp hρ hφ hP2 hfrob h0 h2 0 1
      have hf := c3_formula hρ hφ hfrob h0 h2 hu e
      rw [hk u hu, h4, h6, mul_zero, mul_one, mul_zero, zero_add] at hf
      exact c3_gauss_ne (by omega) hr hz hs (by unfold c3B at hf; exact hf.symm)
  · intro hbit u hu
    obtain ⟨y4, y5, y6, y7⟩ := hpb.1.2 hbit
    have hf := c3_formula hρ hφ hfrob h0 h2 hu e
    unfold c3A c3B at hf
    rw [y4, y5, y6, y7] at hf
    simp only [Int.cast_zero, mul_zero, add_zero, zero_mul] at hf
    exact (mul_eq_zero.1 hf).resolve_left hd

theorem c3_par_ker {K : Type*} [Field K] {A B A' B' s t : K} (hv : ¬ (A = 0 ∧ B = 0))
    (h : A * B' - B * A' = 0) (h1 : A * s + B * t = 0) : A' * s + B' * t = 0 := by
  by_cases hA : A = 0
  · have hB : B ≠ 0 := fun hB => hv ⟨hA, hB⟩
    subst hA
    have e1 : A' = 0 := by simpa [hB] using h
    have e2 : t = 0 := by simpa [hB] using h1
    simp [e1, e2]
  · have : A * (A' * s + B' * t) = 0 := by linear_combination A' * h1 + t * h
    exact (mul_eq_zero.1 this).resolve_left hA

theorem c3_cross {r : ZMod p} (hr : r * r = -1) (e f : ℕ) :
    c3A r e * c3B r f - c3B r e * c3A r f =
      ((crR (Yv E8.V C3.XM e 4) (Yv E8.V C3.XM e 5) (Yv E8.V C3.XM e 6) (Yv E8.V C3.XM e 7)
        (Yv E8.V C3.XM f 4) (Yv E8.V C3.XM f 5) (Yv E8.V C3.XM f 6) (Yv E8.V C3.XM f 7) : ℤ) :
          ZMod p) +
      r * ((crI (Yv E8.V C3.XM e 4) (Yv E8.V C3.XM e 5) (Yv E8.V C3.XM e 6) (Yv E8.V C3.XM e 7)
        (Yv E8.V C3.XM f 4) (Yv E8.V C3.XM f 5) (Yv E8.V C3.XM f 6) (Yv E8.V C3.XM f 7) : ℤ) :
          ZMod p) := by
  unfold c3A c3B crR crI
  push_cast
  linear_combination (((Yv E8.V C3.XM e 5 : ℤ) : ZMod p) * ((Yv E8.V C3.XM f 7 : ℤ) : ZMod p) -
    ((Yv E8.V C3.XM e 7 : ℤ) : ZMod p) * ((Yv E8.V C3.XM f 5 : ℤ) : ZMod p)) * hr

theorem c3_hVl : ∀ g < 240, ∀ m < 8, fld (fld E8.V 128 g) 16 m < 16 := fun g hg =>
  (root_lanes (n := 8) (by norm_num) (ch715750all.e8_root g hg)).1

theorem c3_AB_ne (h7 : 7 ≤ p) {r : ZMod p} (hr : r * r = -1) {e : ℕ} (he : e < 240)
    (hn : C3.SG.testBit e = false) : ¬ (c3A r e = 0 ∧ c3B r e = 0) := by
  rintro ⟨hA, hB⟩
  have hpb := pbE_spec c3_hVl he (pbW_spec ch715750all.c3_root e he)
  rcases (hpb.2 hn).1 with ⟨hz, hs⟩ | ⟨hz, hs⟩
  · exact c3_gauss_ne h7 hr hz hs hA
  · exact c3_gauss_ne h7 hr hz hs hB

theorem c3_reps : ∀ k < 12, fld C3.REPS 8 k < 240 ∧ C3.SG.testBit (fld C3.REPS 8 k) = false := by
  decide +kernel

theorem c3_par_rep {r : ZMod p} (hr : r * r = -1) {e : ℕ} (he : e < 240)
    (hn : C3.SG.testBit e = false) :
    c3A r e * c3B r (fld C3.REPS 8 (fld C3.KE 4 e)) -
      c3B r e * c3A r (fld C3.REPS 8 (fld C3.KE 4 e)) = 0 := by
  have hpb := pbE_spec c3_hVl he (pbW_spec ch715750all.c3_root e he)
  obtain ⟨-, -, -, -, hcR, hcI⟩ := hpb.2 hn
  rw [c3_cross hr, hcR, hcI]
  simp

theorem c3_line_iff (hp : 13 ≤ p)
    (hF4 : orderOf ((2 : ZMod p) ^ F) = 4)
    (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    (hφ : ∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g))
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    (h0 : ∀ u ∈ P, c3pr (fld C3.COLS 8 0) u = 0) (h2 : ∀ u ∈ P, c3pr (fld C3.COLS 8 2) u = 0)
    {u : Fin Tag.E8.rank → ZMod p} (hu : u ∈ P) {e : ℕ} (he : e < 240)
    (hn : C3.SG.testBit e = false) :
    c3pr e u = 0 ↔
      c3A ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 (fld C3.KE 4 e)) * c3pr (fld C3.COLS 8 4) u +
        c3B ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 (fld C3.KE 4 e)) *
          c3pr (fld C3.COLS 8 6) u = 0 := by
  have hr := c3_r_sq hF4
  have hd := c3_unit (p := p) (by omega) c3_bx.1 c3_bx.2.1
  have hk := ((pbE_spec c3_hVl he (pbW_spec ch715750all.c3_root e he)).2 hn).2.1
  have hρr := c3_reps _ hk
  have hpar := c3_par_rep hr he hn
  have hf := c3_formula hρ hφ hfrob h0 h2 hu e
  constructor
  · intro h
    rw [h, mul_zero] at hf
    exact c3_par_ker (c3_AB_ne (by omega) hr he hn) hpar hf.symm
  · intro h
    have hpar' : c3A ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 (fld C3.KE 4 e)) *
        c3B ((2 ^ F : ℕ) : ZMod p) e - c3B ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 (fld C3.KE 4 e)) *
        c3A ((2 ^ F : ℕ) : ZMod p) e = 0 := by linear_combination -hpar
    have h' := c3_par_ker (c3_AB_ne (by omega) hr hρr.1 hρr.2) hpar' h
    rw [h'] at hf
    exact (mul_eq_zero.1 hf).resolve_left hd

theorem c3_reps_det (h7 : 7 ≤ p) {r : ZMod p} (hr : r * r = -1) {i j : ℕ} (hi : i < 12)
    (hj : j < 12) (hij : i < j) :
    c3A r (fld C3.REPS 8 i) * c3B r (fld C3.REPS 8 j) -
      c3B r (fld C3.REPS 8 i) * c3A r (fld C3.REPS 8 j) ≠ 0 := by
  have hR : ∀ k < 12, fld C3.REPS 8 k < 240 := fun k hk => (c3_reps k hk).1
  obtain ⟨hz, hs⟩ := (cls_spec c3_hVl hR ch715752.cls).2.2.2.2 i hi j hj hij
  rw [c3_cross hr]
  exact c3_gauss_ne h7 hr hz hs

theorem c3_par_ortho {K : Type*} [Field K] {A B A' B' s t : K} (hst : ¬ (s = 0 ∧ t = 0))
    (h1 : A * s + B * t = 0) (h2 : A' * s + B' * t = 0) : A * B' - B * A' = 0 := by
  by_cases hs : s = 0
  · have ht : t ≠ 0 := fun ht => hst ⟨hs, ht⟩
    subst hs
    have hB : B = 0 := by simpa [ht] using h1
    have hB' : B' = 0 := by simpa [ht] using h2
    simp [hB, hB']
  · have : (A * B' - B * A') * s = 0 := by linear_combination B' * h1 - B * h2
    exact (mul_eq_zero.1 this).resolve_right hs

theorem c3_rep_unique (h7 : 7 ≤ p) {r : ZMod p} (hr : r * r = -1) {s t : ZMod p}
    (hst : ¬ (s = 0 ∧ t = 0)) {i j : ℕ} (hi : i < 12) (hj : j < 12)
    (h1 : c3A r (fld C3.REPS 8 i) * s + c3B r (fld C3.REPS 8 i) * t = 0)
    (h2 : c3A r (fld C3.REPS 8 j) * s + c3B r (fld C3.REPS 8 j) * t = 0) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (c3_par_ortho hst h1 h2) (c3_reps_det h7 hr hi hj h)
  · exact h
  · exact absurd (c3_par_ortho hst h2 h1) (c3_reps_det h7 hr hj hi h)

theorem c3_lineΦ (hp : 13 ≤ p)
    (hF4 : orderOf ((2 : ZMod p) ^ F) = 4)
    (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    (hφ : ∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g))
    (hP2 : Module.finrank (ZMod p) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    (h0 : ∀ u ∈ P, c3pr (fld C3.COLS 8 0) u = 0) (h2 : ∀ u ∈ P, c3pr (fld C3.COLS 8 2) u = 0)
    {u : Fin Tag.E8.rank → ZMod p} (hu : u ∈ P) (hu0 : u ≠ 0) {k : ℕ} (hk : k < 12)
    (hku : c3A ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 k) * c3pr (fld C3.COLS 8 4) u +
      c3B ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 k) * c3pr (fld C3.COLS 8 6) u = 0) :
    ∀ g, g ∈ mset 240 (Nat.lor C3.SG (C3.CMs k)) ↔
      g < 240 ∧ ∀ v ∈ ({u} : Set (Fin Tag.E8.rank → ZMod p)), c3pr g v = 0 := by
  have hr := c3_r_sq hF4
  have hst : ¬ (c3pr (fld C3.COLS 8 4) u = 0 ∧ c3pr (fld C3.COLS 8 6) u = 0) :=
    fun ⟨a, b⟩ => hu0 (c3_inj hp hρ hφ hfrob h0 h2 hu a b)
  have hR : ∀ k < 12, fld C3.REPS 8 k < 240 := fun k hk => (c3_reps k hk).1
  have hcls := cls_spec c3_hVl hR ch715752.cls
  intro g
  simp only [mset, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, Lane.bit_iff, Lane.nlor,
    Nat.testBit_or, Bool.or_eq_true]
  refine and_congr_right fun hg => ?_
  have hpb := pbE_spec c3_hVl hg (pbW_spec ch715750all.c3_root g hg)
  constructor
  · rintro (hs | hc)
    · exact (c3_ker_iff hp hF4 hρ hφ hP2 hfrob h0 h2 hg).2 hs u hu
    · by_cases hs : C3.SG.testBit g = true
      · exact (c3_ker_iff hp hF4 hρ hφ hP2 hfrob h0 h2 hg).2 hs u hu
      · rw [Bool.not_eq_true] at hs
        obtain ⟨-, hke, hcm, -⟩ := hpb.2 hs
        have e : fld C3.KE 4 g = k := hcls.2.1 g _ hke k hk hcm hc
        rw [c3_line_iff hp hF4 hρ hφ hfrob h0 h2 hu hg hs, e]
        exact hku
  · intro h0g
    by_cases hs : C3.SG.testBit g = true
    · exact Or.inl hs
    · rw [Bool.not_eq_true] at hs
      right
      obtain ⟨-, hke, hcm, -⟩ := hpb.2 hs
      have hl := (c3_line_iff hp hF4 hρ hφ hfrob h0 h2 hu hg hs).1 h0g
      rw [← c3_rep_unique (by omega) hr hst hke hk hl hku]
      exact hcm

theorem c3_lineSG (hp : 13 ≤ p)
    (hF4 : orderOf ((2 : ZMod p) ^ F) = 4)
    (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    (hφ : ∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g))
    (hP2 : Module.finrank (ZMod p) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    (h0 : ∀ u ∈ P, c3pr (fld C3.COLS 8 0) u = 0) (h2 : ∀ u ∈ P, c3pr (fld C3.COLS 8 2) u = 0)
    {u : Fin Tag.E8.rank → ZMod p} (hu : u ∈ P)
    (hno : ∀ k < 12, c3A ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 k) * c3pr (fld C3.COLS 8 4) u +
      c3B ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 k) * c3pr (fld C3.COLS 8 6) u ≠ 0) :
    ∀ g, g ∈ mset 240 C3.SG ↔
      g < 240 ∧ ∀ v ∈ ({u} : Set (Fin Tag.E8.rank → ZMod p)), c3pr g v = 0 := by
  intro g
  simp only [mset, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, Lane.bit_iff]
  refine and_congr_right fun hg => ⟨fun hs => (c3_ker_iff hp hF4 hρ hφ hP2 hfrob h0 h2 hg).2 hs u hu,
    fun h0g => ?_⟩
  by_contra hs
  rw [Bool.not_eq_true] at hs
  have hpb := pbE_spec c3_hVl hg (pbW_spec ch715750all.c3_root g hg)
  exact hno _ (hpb.2 hs).2.1 ((c3_line_iff hp hF4 hρ hφ hfrob h0 h2 hu hg hs).1 h0g)

theorem c3_planeΦ (hp : 13 ≤ p)
    (hF4 : orderOf ((2 : ZMod p) ^ F) = 4)
    (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    (hφ : ∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g))
    (hP2 : Module.finrank (ZMod p) P = 2)
    (hfrob : ∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    (h0 : ∀ u ∈ P, c3pr (fld C3.COLS 8 0) u = 0) (h2 : ∀ u ∈ P, c3pr (fld C3.COLS 8 2) u = 0) :
    ∀ g, g ∈ mset 240 C3.SG ↔
      g < 240 ∧ ∀ v ∈ (P : Set (Fin Tag.E8.rank → ZMod p)), c3pr g v = 0 := by
  intro g
  simp only [mset, Set.mem_setOf_eq, Lane.bit_iff, SetLike.mem_coe]
  exact and_congr_right fun hg => (c3_ker_iff hp hF4 hρ hφ hP2 hfrob h0 h2 hg).symm

end C3Plane

theorem c3pr_smul {p : ℕ} (g : ℕ) (c : ZMod p) (v : Fin Tag.E8.rank → ZMod p) :
    c3pr g (c • v) = c * c3pr g v := by
  unfold c3pr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem c3_a0_mem : ∀ k < 13, bit (Nat.land (C3.LPs k) M240) (fld C3.COLS 8 0) = true := by
  decide +kernel

theorem c3_kerQ {p : ℕ} {Q : Set (Fin Tag.E8.rank → ZMod p)} {Φ : Set ℕ}
    (hΦ : ∀ g, g ∈ Φ ↔ g < 240 ∧ ∀ v ∈ Q, c3pr g v = 0) :
    vecOf Tag.E8.rank E8.V '' Φ = kernelRoots (tcChiQ Tag.E8 p Q) := by
  refine image_eq_kernelRoots e8D Q Φ fun g => ?_
  rw [hΦ g]
  refine and_congr_right fun _ => forall₂_congr fun v _ => ?_
  unfold c3pr
  constructor <;> intro h <;> rw [← h] <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem c3_sub_mem {p : ℕ} {Q : Set (Fin Tag.E8.rank → ZMod p)} {Φ : Set ℕ}
    (hΦ : ∀ g, g ∈ Φ ↔ g < 240 ∧ ∀ v ∈ Q, c3pr g v = 0) :
    ∀ a ∈ Φ, ∀ b ∈ Φ, ∀ c < 240, vecOf Tag.E8.rank E8.V c =
      vecOf Tag.E8.rank E8.V a - vecOf Tag.E8.rank E8.V b → c ∈ Φ := by
  intro a ha b hb c hc hv
  refine (hΦ c).2 ⟨hc, fun v hvQ => ?_⟩
  have e : c3pr c v = c3pr a v - c3pr b v := by
    unfold c3pr
    rw [hv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.sub_apply]
    push_cast
    ring
  rw [e, ((hΦ a).1 ha).2 v hvQ, ((hΦ b).1 hb).2 v hvQ, sub_zero]

theorem c3_comp {p F : ℕ}
    {φ : AddMonoid.End (Fin Tag.E8.rank → ℤ)} {ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    (hiso : ∀ x y, iform (φ x) (φ y) = iform x y) (hρ : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ)
    (hφ : ∀ g < 240, φ (vecOf Tag.E8.rank E8.V g) = vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g))
    {Q : Set (Fin Tag.E8.rank → ZMod p)}
    (hfrob : ∀ v ∈ Q, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j)
    {Φ cr lp : ℕ} (hΦ : ∀ g, g ∈ mset 240 Φ ↔ g < 240 ∧ ∀ v ∈ Q, c3pr g v = 0)
    (h : lnK E8.ADJ C2M.POS C2M.DEC C2P.PW cr Φ (fld C3.COLS 8 0) lp = true) :
    ∃ i : KernelComponent (tcChiQ Tag.E8 p Q),
      componentRoots (tcChiQ Tag.E8 p Q) i =
        vecOf Tag.E8.rank E8.V '' mset 240 (Nat.land lp M240) ∧
      TcDataOK ρ (componentRoots (tcChiQ Tag.E8 p Q) i) (tkCd5 (Nat.shiftRight lp 240)) := by
  obtain ⟨r0, hc, hks⟩ := lnK_spec rfl e8D e8_hX ch715750all.t_q ch715750all.t_mv
    ch715750all.c2m_pos ch715750all.c2m_dec pw_lt (c3_sub_mem hΦ) c3_hVl
    (fun g hg m => cart_row Tag.E8 e8_yc e8_ycb e8_ycl ch715750all.e8_root hg m)
    (fun g hg j => (root_lanes (n := 8) (by norm_num) (ch715750all.e8_root g hg)).2.2.1 j)
    e8_qb h
  have hφr : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (φ γ) := by
    intro γ hγ
    obtain ⟨g, hg, rfl⟩ := e8D.exists_eq hγ
    rw [hφ g hg]
    exact e8D.isRoot _ (pw_lt g hg)
  have hker := kernelRoots_frob_image φ ρ hρ hφr _ Q hfrob
  have hform : ∀ α ∈ kernelRoots (tcChiQ Tag.E8 p Q), ∀ β ∈ kernelRoots (tcChiQ Tag.E8 p Q),
      iform (ρ α) (ρ β) = iform α β := by
    intro α hα β hβ
    rw [hρ _ ((mem_kernelRoots_chiQ p _ α).1 hα).1, hρ _ ((mem_kernelRoots_chiQ p _ β).1 hβ).1,
      hiso]
  exact tcDataOK5_of_compRaw e8D ρ hker hform (c3_kerQ hΦ) pw_lt
    (fun g hg => (hφ g hg).symm.trans (hρ _ (e8D.isRoot g hg)).symm) hc hks

theorem c3_base :
    C3NoSurv (fld C3.COLS 8 0) (fld C3.COLS 8 2) := by
  intro p _ hp13 F hF4 φ ρ hiso hρ hφ P hP2 hfrob iJ ha hb x ix hS
  obtain ⟨-, hxP, hx0, hJx, hne, hsplit, hoth⟩ := hS
  have hr := c3_r_sq hF4
  obtain ⟨hcl, -⟩ := cols_spec ch715752.cols
  have h0 : ∀ u ∈ P, c3pr (fld C3.COLS 8 0) u = 0 := fun u hu =>
    ((mem_kernelRoots_chiQ p _ _).1 ha.1).2 u hu
  have h2 : ∀ u ∈ P, c3pr (fld C3.COLS 8 2) u = 0 := fun u hu =>
    ((mem_kernelRoots_chiQ p _ _).1 hb.1).2 u hu
  have hab : iform (vecOf Tag.E8.rank E8.V (fld C3.COLS 8 0))
      (vecOf Tag.E8.rank E8.V (fld C3.COLS 8 2)) = -1 := by
    rw [← e8_hX _ (hcl 0 (by norm_num)) _ (hcl 2 (by norm_num))]
    decide +kernel
  have hrk2 : ∀ {Ψ : Set (Fin Tag.E8.rank → ℤ)}, IsRootComponent Ψ →
      vecOf Tag.E8.rank E8.V (fld C3.COLS 8 0) ∈ Ψ →
      vecOf Tag.E8.rank E8.V (fld C3.COLS 8 2) ∈ Ψ → 2 ≤ compRank Ψ :=
    fun hΨ ha hb => tc3_compRank_two hΨ ha hb hab
  have ha0 : ∀ k < 13, fld C3.COLS 8 0 ∈ mset 240 (Nat.land (C3.LPs k) M240) :=
    fun k hk => ⟨hcl 0 (by norm_num), c3_a0_mem k hk⟩
  obtain ⟨iJ0, hiJ0, hdJ⟩ := c3_comp (Q := (P : Set (Fin Tag.E8.rank → ZMod p))) hiso hρ hφ
    hfrob (c3_planeΦ hp13 hF4 hρ hφ hP2 hfrob h0 h2) (lnJ_spec ch715752.lineJ).1
  have hJeq : iJ0 = iJ :=
    eq_of_mem_componentRoots (by rw [hiJ0]; exact Set.mem_image_of_mem _ (ha0 12 (by norm_num)))
      ha
  subst hJeq
  have hdJ2 : 2 ≤ (tkCd5 (Nat.shiftRight (C3.LPs 12) 240)).r := by
    rw [hdJ.2.1]
    exact hrk2 (isRootComponent_componentRoots _) ha hb
  have hfx : ∀ v ∈ ({x} : Set (Fin Tag.E8.rank → ZMod p)), ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j := by
    rintro v rfl j
    exact hfrob v hxP j
  by_cases hex : ∃ k < 12, c3A ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 k) *
      c3pr (fld C3.COLS 8 4) x + c3B ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 k) *
      c3pr (fld C3.COLS 8 6) x = 0
  swap
  · push Not at hex
    obtain ⟨i, hi, -⟩ := c3_comp (Q := {x}) hiso hρ hφ hfx
      (c3_lineSG hp13 hF4 hρ hφ hP2 hfrob h0 h2 hxP hex) (lnJ_spec ch715752.lineJ).1
    have hie : i = ix :=
      eq_of_mem_componentRoots (by rw [hi]; exact Set.mem_image_of_mem _ (ha0 12 (by norm_num)))
        (hJx ha)
    subst hie
    exact hne (hi.trans hiJ0.symm)
  obtain ⟨k, hk, hkx⟩ := hex
  obtain ⟨i, hi, hdx⟩ := c3_comp (Q := {x}) hiso hρ hφ hfx
    (c3_lineΦ hp13 hF4 hρ hφ hP2 hfrob h0 h2 hxP hx0 hk hkx) (ch715750all.c3_line k hk)
  have hie : i = ix :=
    eq_of_mem_componentRoots (by rw [hi]; exact Set.mem_image_of_mem _ (ha0 k (by omega)))
      (hJx ha)
  subst hie
  have hdx2 : 2 ≤ (tkCd5 (Nat.shiftRight (C3.LPs k) 240)).r := by
    rw [hdx.2.1]
    exact hrk2 (isRootComponent_componentRoots _) (hJx ha) (hJx hb)
  have hz : ∀ g, c3pr g (0 : Fin Tag.E8.rank → ZMod p) = 0 := fun g => by simp [c3pr]
  refine jok3_spec ch715752.jok k (by omega) ?_ ?_ ?_
  · intro hm
    apply hne
    rw [hi, hiJ0, hm]
  · exact (flagFree_labs hp13 hF4 hdx2).1 (tcrLabs_split_of hdx hsplit)
  · intro y hy hyk
    by_cases hy12 : y = 12
    · subst hy12
      left
      have hmem := tcrLabs_mem_of_dataOK hdJ 1
      rw [List.any_eq_true]
      exact ⟨_, hmem, by simpa using hmem⟩
    have hy' : y < 12 := by omega
    have hABy := c3_AB_ne (by omega) hr (c3_reps y hy').1 (c3_reps y hy').2
    obtain ⟨u, hu, hu4, hu6⟩ := c3_surj hp13 hρ hφ hP2 hfrob h0 h2
      (-c3B ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 y)) (c3A ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 y))
    have hyu : c3A ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 y) * c3pr (fld C3.COLS 8 4) u +
        c3B ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 y) * c3pr (fld C3.COLS 8 6) u = 0 := by
      rw [hu4, hu6]
      ring
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, hz] at hu4 hu6
      exact hABy ⟨hu6.symm, neg_eq_zero.1 hu4.symm⟩
    have hnot : ∀ c : ZMod p, u ≠ c • x := by
      intro c hc
      have hs : ¬ (c3pr (fld C3.COLS 8 4) u = 0 ∧ c3pr (fld C3.COLS 8 6) u = 0) :=
        fun ⟨a, b⟩ => hu0 (c3_inj hp13 hρ hφ hfrob h0 h2 hu a b)
      have hku : c3A ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 k) * c3pr (fld C3.COLS 8 4) u +
          c3B ((2 ^ F : ℕ) : ZMod p) (fld C3.REPS 8 k) * c3pr (fld C3.COLS 8 6) u = 0 := by
        rw [hc, c3pr_smul, c3pr_smul]
        linear_combination c * hkx
      exact hyk (c3_rep_unique (by omega) hr hs hy' hk hyu hku)
    have hfu : ∀ v ∈ ({u} : Set (Fin Tag.E8.rank → ZMod p)), ∀ j : Fin Tag.E8.rank,
        ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j := by
      rintro v rfl j
      exact hfrob v hu j
    obtain ⟨iu, hiu, hdu⟩ := c3_comp (Q := {u}) hiso hρ hφ hfu
      (c3_lineΦ hp13 hF4 hρ hφ hP2 hfrob h0 h2 hu hu0 hy' hyu) (ch715750all.c3_line y hy')
    have hau : vecOf Tag.E8.rank E8.V (fld C3.COLS 8 0) ∈ componentRoots (tcChiLn Tag.E8 p u) iu := by
      rw [hiu]
      exact Set.mem_image_of_mem _ (ha0 y hy)
    have hsub : componentRoots (tcChiPl Tag.E8 p P) iJ0 ⊆ componentRoots (tcChiLn Tag.E8 p u) iu :=
      componentRoots_subset_of_kernel_subset
        (kernelRoots_chiQ_mono (Set.singleton_subset_iff.2 hu)) ha hau
    have hdu2 : 2 ≤ (tkCd5 (Nat.shiftRight (C3.LPs y) 240)).r := by
      rw [hdu.2.1]
      exact hrk2 (isRootComponent_componentRoots _) (hsub ha) (hsub hb)
    rcases hoth u hu hu0 hnot iu hsub with hov | hhalf
    · left
      exact (flagFree_labs hp13 hF4 hdJ2).2.2 _ hdu2 (tcrLabs_overlap_of hdu hdJ hov)
    · right
      exact (flagFree_labs hp13 hF4 hdu2).2.1 (tcrLabs_half_of hdu hhalf)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes in
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit) in
open CFSG.StandardType (GGLabelIso) in
theorem certificate715752_of_checks :
 ∀ {p : ℕ} [Fact p.Prime], 13 ≤ p → ∀ {F : ℕ}, orderOf ((2 : ZMod p) ^ F) = 4 →
    ∀ (φ : AddMonoid.End (Fin Tag.E8.rank → ℤ)), (∀ x y, iform (φ x) (φ y) = iform x y) →
    (∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (φ γ)) → (∀ x, φ (φ x) = -x) →
    ∀ (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)), (∀ x, ρ x = φ x) →
    ∀ (P : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p)), Module.finrank (ZMod p) P = 2 →
    (∀ v ∈ P, ∀ j : Fin Tag.E8.rank,
      ∑ k, ((ρ (Pi.single j 1) k : ℤ) : ZMod p) * v k = ((2 ^ F : ℕ) : ZMod p) * v j) →
    ∀ (iJ : KernelComponent (tcChiPl Tag.E8 p P)),
    2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl Tag.E8 p P) iJ) →
    (∃ a ∈ componentRoots (tcChiPl Tag.E8 p P) iJ,
      ∃ b ∈ componentRoots (tcChiPl Tag.E8 p P) iJ, iform a b = -1) →
    ∀ {x : Fin Tag.E8.rank → ZMod p}, x ∈ P → x ≠ 0 →
    ∀ (ix : KernelComponent (tcChiLn Tag.E8 p x)),
    componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p x) ix →
    componentRoots (tcChiLn Tag.E8 p x) ix ≠ componentRoots (tcChiPl Tag.E8 p P) iJ →
    (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 p x) ix)) ∧
      LargeEvenSplit p lab') →
    (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod p, d ≠ c • x) →
      ∀ i : KernelComponent (tcChiLn Tag.E8 p d),
      componentRoots (tcChiPl Tag.E8 p P) iJ ⊆ componentRoots (tcChiLn Tag.E8 p d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn Tag.E8 p d) i))
        (LabAt ρ F (componentRoots (tcChiPl Tag.E8 p P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn Tag.E8 p d) i)) ∧
        LargeEvenHalfSplit p lab' c) → False := by
  intro p _ hp13 F hF4 φ hiso hroot hsq ρ hρ P hP2 hfrob iJ hJ2 hab x hxP hx0 ix hJx hne hsplit
    hoth
  have hρr : ∀ γ, IsRoot Tag.E8 γ → ρ γ = φ γ := fun γ _ => hρ γ
  have hS : SurvHyp ρ F P iJ x ix := ⟨hJ2, hxP, hx0, hJx, hne, hsplit, hoth⟩
  obtain ⟨h, hh⟩ := exists_conj_phi0 e8D c2_search (t0_lt 0 (by norm_num)) e8_beta0 φ hiso hsq
    hroot
  let ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ) := tcrWEnd Tag.E8 h * φ * tcrWEnd Tag.E8 h⁻¹
  have hψ : ∀ y, ψ y = h • φ (h⁻¹ • y) := fun _ => rfl
  have hiso' : ∀ a b, iform (ψ a) (ψ b) = iform a b := by
    intro a b
    rw [hψ, hψ, iform_smul, hiso, iform_smul]
  have hroot' : ∀ γ, IsRoot Tag.E8 γ → IsRoot Tag.E8 (ψ γ) := fun γ hγ => by
    rw [hψ]
    exact IsRoot.smul (hroot _ (IsRoot.smul hγ h⁻¹)) h
  have hψ2 : ∀ y, ψ (ψ y) = -y := by
    intro y
    rw [hψ (ψ y), hψ y, inv_smul_smul, hsq, smul_neg, smul_inv_smul]
  have hρ' : ∀ y, tcrConjPerm h ρ y = ψ y := by
    intro y
    rw [tcrConjPerm_apply, hρ, hψ]
  have hρ'r : ∀ γ, IsRoot Tag.E8 γ → tcrConjPerm h ρ γ = ψ γ := fun γ _ => hρ' γ
  have hpw := pw8_spec e8D ch715750all.e8_root ch715751p.pw ψ hiso' hh t0_lt
  have hpwv : ∀ g < 240, vecOf Tag.E8.rank E8.V (fld C2P.PW 8 g) =
      ψ (vecOf Tag.E8.rank E8.V g) := fun g hg => (hpw g hg).2
  obtain ⟨iJ', ix', hiJ', -, hS'⟩ := SurvHyp.conj h hS
  have hfrob' := tcrDual_frob h φ ρ hρr (((2 ^ F : ℕ) : ZMod p)) P hfrob
  have hP2' : Module.finrank (ZMod p) (P.map (tcrDualLin h p)) = 2 := by
    rw [finrank_map_tcrDualLin]
    exact hP2
  have hkerI : kernelRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))) =
      tcrConjPerm h ρ '' kernelRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))) :=
    kernelRoots_frob_image ψ (tcrConjPerm h ρ) hρ'r hroot' (((2 ^ F : ℕ) : ZMod p))
      ((P.map (tcrDualLin h p) : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p)) :
        Set (Fin Tag.E8.rank → ZMod p)) hfrob'
  have hstab : ∀ γ ∈ kernelRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))),
      tcrConjPerm h ρ γ ∈ kernelRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))) := by
    intro γ hγ
    rw [hkerI]
    exact Set.mem_image_of_mem _ hγ
  have hform : ∀ γ δ, iform (tcrConjPerm h ρ γ) (tcrConjPerm h ρ δ) = iform γ δ := by
    intro γ δ
    rw [hρ' γ, hρ' δ]
    exact hiso' γ δ
  obtain ⟨j, hj⟩ := exists_image_component_of_stable
    (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))) hstab hform iJ'
  have hij : iJ' ≠ j := by
    intro hEq
    rw [← hEq] at hj
    exact image_ne_of_two_le_componentOrbitLength hS'.1 hj
  have hort : ∀ γ ∈ componentRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))) iJ',
      ∀ δ ∈ componentRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))) iJ',
        iform γ (ψ δ) = 0 := by
    intro γ hγ δ hδ
    have hδ' : ψ δ ∈ componentRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))) j := by
      rw [← hj]
      exact ⟨δ, hδ, hρ' δ⟩
    exact iform_eq_zero_of_mem_componentRoots' hij hγ hδ'
  obtain ⟨a, haJ, b, hbJ, hab1⟩ := hab
  have haJ' : h • a ∈ componentRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))) iJ' := by
    rw [hiJ']
    exact ⟨a, haJ, rfl⟩
  have hbJ' : h • b ∈ componentRoots (tcChiPl Tag.E8 p (P.map (tcrDualLin h p))) iJ' := by
    rw [hiJ']
    exact ⟨b, hbJ, rfl⟩
  have hab' : iform (h • a) (h • b) = -1 := by
    rw [iform_smul]
    exact hab1
  obtain ⟨ia, hia, hiaeq⟩ := e8D.exists_eq ((mem_kernelRoots_chiQ p _ _).1 haJ'.1).1
  obtain ⟨ib, hib, hibeq⟩ := e8D.exists_eq ((mem_kernelRoots_chiQ p _ _).1 hbJ'.1).1
  have hadm : Adm (vecOf Tag.E8.rank E8.V) C2P.PW ia ib := by
    refine ⟨hia, hib, ?_, ?_, ?_, ?_⟩
    · rw [hpwv ia hia, CFSG.LieType.Steinberg.Adjoint.iform_comm]
      exact tch_skew_self ψ hiso' hψ2 _
    · rw [hpwv ib hib, CFSG.LieType.Steinberg.Adjoint.iform_comm]
      exact tch_skew_self ψ hiso' hψ2 _
    · rw [hiaeq, hibeq, CFSG.LieType.Steinberg.Adjoint.iform_comm]
      exact hab'
    · rw [hpwv ia hia, hibeq, hiaeq]
      exact hort _ hbJ' _ haJ'
  have hVl : ∀ i < 240, ∀ m < 8, fld (fld E8.V 128 i) 16 m < 16 := fun i hi =>
    (root_lanes (n := 8) (by norm_num) (ch715750all.e8_root i hi)).1
  have hmvf : ∀ y < 240, ∀ f : ℕ, mvf E8T.MVS y f = lsum (fun i =>
      if iform (vecOf Tag.E8.rank E8.V i) (vecOf Tag.E8.rank E8.V y) + 2 = f then 1 else 0) :=
    fun y hy f => mv_fld e8D rfl hVl
      (fun g hg m => cart_row Tag.E8 e8_yc e8_ycb e8_ycl ch715750all.e8_root hg m)
      (fun g hg j => (root_lanes (n := 8) (by norm_num) (ch715750all.e8_root g hg)).2.2.1 j)
      e8_qb ch715750all.t_q ch715750all.t_mv hy f
  obtain ⟨hcl, -⟩ := cols_spec ch715752.cols
  obtain ⟨ks, hks, hka, hkb⟩ := adm_reach hmvf (fun g hg => (hpw g hg).1) c3_hPG
    (hcl 0 (by norm_num)) (hcl 2 (by norm_num)) ch715752.zl ch715752.cnt ch715750all.c3_leaf hadm
  have hfin : C3NoSurv ia ib := by
    rw [hka, hkb]
    exact c3NoSurv_wapp (hcl 0 (by norm_num)) (hcl 2 (by norm_num)) c3_base ks hks
  unfold C3NoSurv at hfin
  exact hfin (p := p) hp13 hF4 ψ (tcrConjPerm h ρ) hiso' hρ'r (fun g hg => (hpwv g hg).symm) _ hP2'
    hfrob' iJ'
    (by rw [hiaeq]; exact haJ') (by rw [hibeq]; exact hbJ') _ ix' hS'

end CFSG.KC.TcRes

end
