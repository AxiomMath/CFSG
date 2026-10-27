module

public import Certificates.Kernel.Sporadic.Fi22.Pump36908K
public import Certificates.Kernel.Sporadic.Fi22.Pump36908F
public import Certificates.Kernel.Sporadic.Fi22.Five8124G
public import Certificates.Kernel.Sporadic.Fi22.WordKit
public import Certificates.Kernel.Fi22Reps.Final
public import CFSG.Certificates.Kernel.Misc.PtOrbFSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Pump36908

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Fi22Pump CFSG.KC.PtOrb CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fv8124
open CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.KC.Fv8124
open CertificateChecks.KernelFi22Reps (LT xT LTRep rep_xT smul_val)
open CFSG.KD.Fi22S0 (RepE)
open CFSG.KC.Fi22S0 (ent)
open CFSG.Sporadic.Fi22 (J a b)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three (xRep)
open scoped commutatorElement

theorem cntN_succ (T : ℕ → ℕ) (n : ℕ) :
    cntN T (n + 1) = cntN T n + if T n = n then 1 else 0 := by
  change Nat.add (cntN T n) (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (T n) n)) = _
  cases h : Nat.beq (T n) n
  · have hne : T n ≠ n := fun e => by
      rw [e, Nat.beq_refl] at h
      exact Bool.noConfusion h
    rw [if_neg hne]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

theorem cntN_eq_card (T : ℕ → ℕ) (n : ℕ) : cntN T n = Nat.card {x : Fin n // T x = x} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if T i = i then 1 else 0) n]
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih, cntN_succ]

theorem card_fix {t : ℕ} {g : J} (hT : RepE t g) :
    Nat.card {v : Fin 3510 // g • v = v} = cntF (ent t) := by
  rw [cntF, cntN_eq_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  rw [CFSG.KD.Fi22Reps.repE_iff.1 hT v v.2, smul_val g v.2, Fin.eta]
  exact ⟨fun e => congrArg Fin.val e, Fin.ext⟩

theorem card_fix_pe {t : ℕ} (ht : PP 3510 12 t) :
    Nat.card {v : Fin 3510 // pe t v = v} = cntF (ev t) := by
  rw [cntF, cntN_eq_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  rw [← pe_apply ht]
  exact ⟨fun e => congrArg Fin.val e, Fin.ext⟩

theorem pG {k : ℕ} (hk : k < 2) : PP 3510 12 (Fi22CGT.F k) :=
  PP_of_permOK hsz (allN_spec Fi22W.permG k hk)

theorem gen_pe {k : ℕ} (hk : k < 2) : fi22GenPerm k = pe (Fi22CGT.F k) := by
  unfold fi22GenPerm pe
  rw [Fi22W.gen_eq hk]
  rfl

theorem smul_ent {t : ℕ} {g : J} (hT : RepE t g) (v : Fin 3510) :
    ((g • v : Fin 3510) : ℕ) = ent t v := by
  rw [CFSG.KD.Fi22Reps.repE_iff.1 hT v v.2, smul_val g v.2, Fin.eta]

theorem sigC_spec {S A G : ℕ → ℕ} (h : sigC S A G = true) {x : ℕ} (hx : x < 3510) :
    S (A x) = G (S x) := by
  unfold sigC at h
  exact Nat.eq_of_beq_eq_true (allN_spec' h hx)

theorem commC_spec {Y X : ℕ → ℕ} (h : commC Y X = true) {x : ℕ} (hx : x < 3510) :
    Y (X x) = X (Y x) := by
  unfold commC at h
  exact Nat.eq_of_beq_eq_true (allN_spec' h hx)

theorem orbC_spec {f : ℕ → ℕ → ℕ} {k r x c : ℕ} (h : orbC f k r x c = true) :
    orbClosed f k 3510 r x = true ∧ popF (closeF f k 3510 r (Nat.shiftLeft 1 x)) 3510 = c := by
  unfold orbC at h
  rw [Fv8124.strictB_eq] at h
  unfold orbClosed
  rw [Fv8124.strictB_eq]
  revert h
  cases closedF f k (nat_lit 3510) (closeF f k (nat_lit 3510) r (Nat.shiftLeft (nat_lit 1) x))
  · intro h
    exact Bool.noConfusion h
  · intro h
    exact ⟨rfl, Nat.eq_of_beq_eq_true h⟩

section Generic

variable {n : ℕ}

theorem app2 (f g : Equiv.Perm (Fin n)) (x : Fin n) : (f * g) x = f (g x) := rfl

theorem app3 (f g h : Equiv.Perm (Fin n)) (x : Fin n) : (f * g * h) x = f (g (h x)) := rfl

theorem toPerm_app {G : Type*} [Group G] [MulAction G (Fin n)] (g : G) (x : Fin n) :
    (MulAction.toPerm g : Equiv.Perm (Fin n)) x = g • x := rfl

theorem ext_val {f g : Equiv.Perm (Fin n)} (h : ∀ x : Fin n, (f x : ℕ) = g x) : f = g :=
  Equiv.ext fun x => Fin.ext (h x)

theorem pow3_app {f : Equiv.Perm (Fin n)} (h : f ^ 3 = 1) (x : Fin n) : f (f (f x)) = x := by
  have e := congrArg (fun g : Equiv.Perm (Fin n) => g x) h
  simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using e

theorem comm_app {f g : Equiv.Perm (Fin n)} (h : f * g = g * f) (x : Fin n) :
    f (g x) = g (f x) :=
  congrArg (fun k : Equiv.Perm (Fin n) => k x) h

end Generic

theorem sigma_eq {s A G : ℕ} {g : J} (hs : PP 3510 12 s) (hG : PP 3510 12 G) (hA : RepE A g)
    (h : sigC (ev s) (ent A) (ev G) = true) : pe s * MulAction.toPerm g = pe G * pe s := by
  refine ext_val fun v => ?_
  rw [app2, app2, toPerm_app, pe_apply hs, pe_apply hG, pe_apply hs, smul_ent hA]
  exact sigC_spec h v.2

theorem X_apply {s t : ℕ} {g : J} (hs : PP 3510 12 s) (hT : RepE t g) (v : Fin 3510) :
    (((pe s * MulAction.toPerm g * (pe s)⁻¹ : Equiv.Perm (Fin 3510)) v : Fin 3510) : ℕ) =
      ev s (ent t (ev (Fi22X.inv s) v)) := by
  rw [← pe_inv hs, app3, toPerm_app, pe_apply hs, smul_ent hT, pe_apply (PP_inv hs)]

theorem lt_mem {s : Set (Equiv.Perm (Fin 3510))} {g : Equiv.Perm (Fin 3510)}
    (hg : g ∈ s) : g ∈ Subgroup.closure s := Subgroup.subset_closure hg

theorem okS' : isP S = true ∧ sigC (ev S) (ent (LT 0)) (ev (Fi22CGT.F 0)) = true ∧
    sigC (ev S) (ent (LT 1)) (ev (Fi22CGT.F 1)) = true := by
  have h := okS
  simp only [Fv8124.strictB_eq] at h
  unfold chkS at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem pS : PP 3510 12 S := PP_of_isP okS'.1

theorem sigmaArr_eq : CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.sigmaArr () =
    unpack 3510 12 S := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound Fi22PumpT.all 0 (by norm_num)
  rw [← Fi22PumpT.eq, Nat.mul_zero] at h
  exact h

theorem rep_sigma : ∀ v : Fin 3510,
    (CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.sigmaArr ())[(v : ℕ)]! = pe S v := by
  rw [sigmaArr_eq]
  exact rep_pe pS

theorem okY' {j : ℕ} (hj : j < 2) : chkY S (Fi22X.inv S) (xT 3) (Y j) = true := by
  have h := okY
  simp only [Fv8124.strictB_eq] at h
  exact allN_spec' h hj

theorem letJ0 : CFSG.KD.Fi22Reps.letJ 0 = a := by simp [CFSG.KD.Fi22Reps.letJ]

theorem letJ1 : CFSG.KD.Fi22Reps.letJ 1 = b := by simp [CFSG.KD.Fi22Reps.letJ]

theorem sigma_facts : pe S * MulAction.toPerm a = fi22GenPerm 0 * pe S ∧
    pe S * MulAction.toPerm b = fi22GenPerm 1 * pe S := by
  obtain ⟨-, h0, h1⟩ := okS'
  have r0 := LTRep 0
  have r1 := LTRep 1
  rw [letJ0] at r0
  rw [letJ1] at r1
  rw [gen_pe (by norm_num), gen_pe (by norm_num)]
  exact ⟨sigma_eq pS (pG (by norm_num)) r0 h0, sigma_eq pS (pG (by norm_num)) r1 h1⟩

theorem fix_facts : Nat.card {v : Fin 3510 // xRep 0 • v = v} = 0 ∧
    Nat.card {v : Fin 3510 // xRep 1 • v = v} = 27 ∧
    Nat.card {v : Fin 3510 // xRep 2 • v = v} = 36 ∧
    Nat.card {v : Fin 3510 // xRep 3 • v = v} = 126 := by
  have c0 := okC0
  have c1 := okC1
  have c2 := okC2
  have c3 := okC3
  simp only [Fv8124.strictB_eq] at c0 c1 c2 c3
  rw [card_fix (rep_xT (by norm_num)), card_fix (rep_xT (by norm_num)),
    card_fix (rep_xT (by norm_num)), card_fix (rep_xT (by norm_num))]
  exact ⟨Nat.eq_of_beq_eq_true c0, Nat.eq_of_beq_eq_true c1, Nat.eq_of_beq_eq_true c2,
    Nat.eq_of_beq_eq_true c3⟩

theorem y_facts {j : ℕ} (hj : j < 2) :
    PP 3510 12 (Y j) ∧ pe (Y j) ∈ fi22P ∧ orderOf (pe (Y j)) = 5 ∧
      pe (Y j) * (pe S * MulAction.toPerm (xRep 3) * (pe S)⁻¹) =
        pe S * MulAction.toPerm (xRep 3) * (pe S)⁻¹ * pe (Y j) := by
  have h := okY' hj
  unfold chkY at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hp, hs⟩, h5⟩, h1⟩, hc⟩ := h
  have pY := PP_of_isP hp
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨pY, (mem_P pY).2 hs, orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [← pe_pw pY, ← pe_id]
    exact (pe_eq_iff (PP_pw pY 5) PP_id).2 h5
  · rw [← pe_id]
    exact ne_of pY PP_id h1
  · have hT := rep_xT (k := 3) (by norm_num)
    refine ext_val fun v => ?_
    rw [app2 (pe (Y j)), app2 _ (pe (Y j)), pe_apply pY, X_apply pS hT, X_apply pS hT,
      pe_apply pY]
    exact commC_spec hc v.2

theorem gens_eq (f g : Equiv.Perm (Fin 3510)) :
    Subgroup.closure ({f, g} : Set (Equiv.Perm (Fin 3510))) =
      Subgroup.closure {h | ∃ j < 2, (Bool.rec (motive := fun _ => Equiv.Perm (Fin 3510)) g f
        (Nat.beq j 0)) = h} := by
  congr 1
  ext h
  constructor
  · rintro (rfl | rfl)
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩]
  · rintro ⟨j, hj, rfl⟩
    interval_cases j
    exacts [Or.inl rfl, Or.inr rfl]

theorem gY_eq {y0 y1 : ℕ} {f g : Equiv.Perm (Fin 3510)} (h0 : ∀ x : Fin 3510, ev y0 x = f x)
    (h1 : ∀ x : Fin 3510, ev y1 x = g x) : ∀ j < 2, ∀ x : Fin 3510,
      gY y0 y1 j x = ((Bool.rec (motive := fun _ => Equiv.Perm (Fin 3510)) g f (Nat.beq j 0)) x :
        ℕ) := by
  intro j hj x
  interval_cases j
  · exact h0 x
  · exact h1 x

theorem card_orbit_le (G : Subgroup (Equiv.Perm (Fin 3510))) (x : Fin 3510) :
    Nat.card (MulAction.orbit G x) ≤ Nat.card G := by
  refine Nat.card_le_card_of_surjective (fun m => (⟨m • x, MulAction.mem_orbit _ m⟩ :
      MulAction.orbit G x)) ?_
  rintro ⟨y, m, rfl⟩
  exact ⟨m, rfl⟩

theorem card_pair_gen {y0 y1 c : ℕ} {f g : Equiv.Perm (Fin 3510)}
    (h0 : ∀ x : Fin 3510, ev y0 x = f x) (h1 : ∀ x : Fin 3510, ev y1 x = g x)
    (h : orbC (gY y0 y1) 2 16 1 c = true) :
    c ≤ Nat.card (Subgroup.closure ({f, g} : Set (Equiv.Perm (Fin 3510)))) := by
  obtain ⟨hc, hpop⟩ := orbC_spec h
  have e := (card_orbit (gens_eq f g) (gY_eq h0 h1) (by norm_num : 1 < 3510) hc).trans hpop
  rw [← e, gens_eq f g]
  exact card_orbit_le _ _

theorem card_pair : 1260 ≤ Nat.card (Subgroup.closure
    ({pe (Y 0), pe (Y 1)} : Set (Equiv.Perm (Fin 3510)))) := by
  have pY0 : PP 3510 12 (Y 0) := PP_of_isP (by
    have h := okY' (j := 0) (by norm_num)
    unfold chkY at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1.1)
  have pY1 : PP 3510 12 (Y 1) := PP_of_isP (by
    have h := okY' (j := 1) (by norm_num)
    unfold chkY at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1.1)
  have h := okO
  simp only [Fv8124.strictB_eq] at h
  exact card_pair_gen (fun x => (pe_apply pY0 x).symm) (fun x => (pe_apply pY1 x).symm) h

theorem pump_facts :
    ∃ σ : Equiv.Perm (Fin 3510),
      (∀ v : Fin 3510,
        (CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.sigmaArr ())[(v : ℕ)]! = σ v) ∧
      σ * MulAction.toPerm a = fi22GenPerm 0 * σ ∧
      σ * MulAction.toPerm b = fi22GenPerm 1 * σ ∧
      ∃ Y₁ Y₂ : Equiv.Perm (Fin 3510), Y₁ ∈ fi22P ∧ Y₂ ∈ fi22P ∧ orderOf Y₁ = 5 ∧
        orderOf Y₂ = 5 ∧
        Y₁ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₁ ∧
        Y₂ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₂ ∧
        1080 < Nat.card (Subgroup.closure ({Y₁, Y₂} : Set (Equiv.Perm (Fin 3510)))) := by
  obtain ⟨-, m0, o0, c0⟩ := y_facts (j := 0) (by norm_num)
  obtain ⟨-, m1, o1, c1⟩ := y_facts (j := 1) (by norm_num)
  exact ⟨pe S, rep_sigma, sigma_facts.1, sigma_facts.2, pe (Y 0), pe (Y 1), m0, m1, o0, o1, c0, c1,
    lt_of_lt_of_le (by norm_num) card_pair⟩

theorem q2_mem : pe Q2 ∈ fi22FiveQ := by
  unfold fi22FiveQ fi22FiveQGenArrs
  rw [permsA_two, q2Arr_eq]
  exact lt_mem (Or.inr rfl)

theorem row_facts {i : ℕ} (hi : i < 60) :
    rowF (ev (Fv8124E.T i)) (ev Q2) fi22FiveKeyPts (Nat.beq (Fv8124E.T i) idP) = true := by
  have h := okF
  rw [Fv8124.strictB_eq] at h
  unfold rowsF at h
  have h' := allN_spec' h hi
  rw [Fv8124.strictB_eq] at h'
  exact h'

theorem mem_D0_of_three
    {Z : Equiv.Perm (Fin 3510)} (hZP : Z ∈ fi22P)
    (hZ3 : Z ^ 3 = 1) (hZx : Z * pe Q1 = pe Q1 * Z) : Z ∈ D0 := by
  have H0 := recHyp0
  have hZC : Z ∈ Subgroup.closure ({pe Q1, pe A, pe Q2, pe W} : Set (Equiv.Perm (Fin 3510))) := by
    rw [H0.C_eq]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hZx, H0.hPR hZP⟩
  have hDC : D0 ≤ Subgroup.closure ({pe Q1, pe A, pe Q2, pe W} : Set (Equiv.Perm (Fin 3510))) :=
    H0.D_le_C
  have hcomm := H0.D_eq
  have hcard := H0.C_facts.1
  have hcD : Nat.card D0 = 60 := H0.dCard
  generalize Subgroup.closure ({pe Q1, pe A, pe Q2, pe W} : Set (Equiv.Perm (Fin 3510))) = C
    at hZC hDC hcomm hcard
  have hcardD : Nat.card (D0.subgroupOf C) = 60 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
    exact hcD
  have hidx : (D0.subgroupOf C).index = 20 := by
    have h := Subgroup.card_mul_index (D0.subgroupOf C)
    rw [hcardD, hcard] at h
    omega
  have hN : (D0.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : ⁅(g : Equiv.Perm (Fin 3510)), (n : Equiv.Perm (Fin 3510))⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator g.2 n.2
    rw [hcomm] at h1
    have e : ((g * n * g⁻¹ : C) : Equiv.Perm (Fin 3510)) =
        ⁅(g : Equiv.Perm (Fin 3510)), (n : Equiv.Perm (Fin 3510))⁆ * n := by
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [e]
    exact D0.mul_mem h1 hn⟩
  let z : C := ⟨Z, hZC⟩
  have hz3 : z ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hZ3)
  have h20 := Subgroup.pow_index_mem (D0.subgroupOf C) z
  rw [hidx] at h20
  have e : z = (z ^ 20)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ', show 20 + 1 = 3 * 7 from rfl, pow_mul, hz3, one_pow]
  have hzD : z ∈ D0.subgroupOf C := by
    rw [e]
    exact Subgroup.inv_mem _ h20
  exact Subgroup.mem_subgroupOf.1 hzD

theorem line0 : fi22FiveLine 0 = pe Q1 := by
  rw [line_eq']
  exact lineE_zero _ _

theorem no_move {t : ℕ} (pT : PP 3510 12 t) (h3 : pe t ^ 3 = 1) {p : ℕ} (hp : p < 3510) :
    Nat.beq (ev t (ev t (ev t p))) p = true := by
  have e := congrArg Fin.val (pow3_app h3 ⟨p, hp⟩)
  rw [pe_apply pT, pe_apply pT, pe_apply pT] at e
  change ev t (ev t (ev t p)) = p at e
  rw [e, Nat.beq_refl]

theorem comm_of_commC {t q : ℕ} (pT : PP 3510 12 t) (pq : PP 3510 12 q)
    (hc : pe t * pe q = pe q * pe t) : commC (ev t) (ev q) = true := by
  unfold commC
  refine Orb.allN_iff.2 fun x hx => ?_
  have e := congrArg Fin.val (comm_app hc ⟨x, hx⟩)
  rw [pe_apply pT, pe_apply pq, pe_apply pq, pe_apply pT] at e
  change ev t (ev q x) = ev q (ev t x) at e
  change Nat.beq (ev t (ev q x)) (ev q (ev t x)) = true
  rw [e, Nat.beq_refl]

theorem row_conc {t : ℕ}
    (pT : PP 3510 12 t) (h3 : pe t ^ 3 = 1) (ho : orderOf (pe t) = 3)
    (h : rowF (ev t) (ev Q2) fi22FiveKeyPts (Nat.beq t idP) = true) :
    Nat.card {v : Fin 3510 // pe t v = v} = 126 ∧ ∃ q ∈ fi22FiveQ, pe t * q ≠ q * pe t := by
  unfold rowF at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true'] at h
  rcases h with (⟨p, hp, hmv⟩ | hid) | ⟨hcnt, hnc⟩
  · rw [no_move pT h3 (key_lt p hp)] at hmv
    exact Bool.noConfusion hmv
  · have e1 : pe t = 1 := by
      rw [← pe_id]
      exact (pe_eq_iff pT PP_id).2 hid
    rw [e1, orderOf_one] at ho
    exact absurd ho (by norm_num)
  · refine ⟨by rw [card_fix_pe pT]; exact Nat.eq_of_beq_eq_true hcnt, pe Q2, q2_mem, fun hc => ?_⟩
    rw [comm_of_commC pT pQ2 hc] at hnc
    exact Bool.noConfusion hnc

theorem five_facts :
    ∀ Z ∈ fi22P, orderOf Z = 3 → Z * fi22FiveLine 0 = fi22FiveLine 0 * Z →
      Nat.card {v : Fin 3510 // Z v = v} = 126 ∧ ∃ q ∈ fi22FiveQ, Z * q ≠ q * Z := by
  intro Z hZP hZ3 hZx
  rw [line0] at hZx
  have hZ3' : Z ^ 3 = 1 := by
    rw [← hZ3]
    exact pow_orderOf_eq_one Z
  obtain ⟨i, hi, rfl⟩ := mem_D0.1 (mem_D0_of_three hZP hZ3' hZx)
  exact row_conc (Fv8124.pT i hi) hZ3' hZ3 (row_facts hi)

theorem facts :
    (∃ σ : Equiv.Perm (Fin 3510),
        (∀ v : Fin 3510,
          (CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.sigmaArr ())[(v : ℕ)]! = σ v) ∧
        σ * MulAction.toPerm a = fi22GenPerm 0 * σ ∧
        σ * MulAction.toPerm b = fi22GenPerm 1 * σ ∧
        ∃ Y₁ Y₂ : Equiv.Perm (Fin 3510), Y₁ ∈ fi22P ∧ Y₂ ∈ fi22P ∧ orderOf Y₁ = 5 ∧
          orderOf Y₂ = 5 ∧
          Y₁ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₁ ∧
          Y₂ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₂ ∧
          1080 < Nat.card (Subgroup.closure ({Y₁, Y₂} : Set (Equiv.Perm (Fin 3510))))) ∧
    Nat.card {v : Fin 3510 // xRep 0 • v = v} = 0 ∧
    Nat.card {v : Fin 3510 // xRep 1 • v = v} = 27 ∧
    Nat.card {v : Fin 3510 // xRep 2 • v = v} = 36 ∧
    Nat.card {v : Fin 3510 // xRep 3 • v = v} = 126 ∧
    ∀ Z ∈ fi22P, orderOf Z = 3 → Z * fi22FiveLine 0 = fi22FiveLine 0 * Z →
      Nat.card {v : Fin 3510 // Z v = v} = 126 ∧ ∃ q ∈ fi22FiveQ, Z * q ≠ q * Z :=
  ⟨pump_facts, fix_facts.1, fix_facts.2.1, fix_facts.2.2.1, fix_facts.2.2.2, five_facts⟩

end CertificateChecks.KernelSpor.Pump36908

end
