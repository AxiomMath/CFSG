
module

public import Certificates.Kernel.Ks2.Checks
public import Certificates.Kernel.KsEight.SylGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKs2Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKs2.G

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.EvenSporadicStandard.Fin76b.U16
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CentBound
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut CertificateChecks.KernelKs2
open CertificateChecks.KernelCU43Aut.CentG CertificateChecks.KernelCU43Aut.SylG
open CertificateChecks.KernelKsEight.CentG8 CertificateChecks.KernelKsEight.SylG8

theorem twist_inv {G : Type*} [Group G] {a b : G} (h : a * b = b⁻¹ * a) : a * b⁻¹ = b * a :=
  calc a * b⁻¹ = b * (b⁻¹ * a) * b⁻¹ := by group
    _ = b * (a * b) * b⁻¹ := by rw [← h]
    _ = b * a := by group

theorem twist_inv' {G : Type*} [Group G] {a b : G} (h : a * b = b⁻¹ * a) : a⁻¹ * b = b⁻¹ * a⁻¹ :=
  calc a⁻¹ * b = a⁻¹ * (b * a) * a⁻¹ := by group
    _ = a⁻¹ * (a * b⁻¹) * a⁻¹ := by rw [twist_inv h]
    _ = b⁻¹ * a⁻¹ := by group

theorem comm_of_twists {G : Type*} [Group G] {x ξ ν : G} (hx : x * ν = ν⁻¹ * x)
    (hξ : ξ * ν = ν⁻¹ * ξ) : x * ξ⁻¹ * ν = ν * (x * ξ⁻¹) :=
  calc x * ξ⁻¹ * ν = x * (ξ⁻¹ * ν) := by group
    _ = x * (ν⁻¹ * ξ⁻¹) := by rw [twist_inv' hξ]
    _ = x * ν⁻¹ * ξ⁻¹ := by group
    _ = ν * x * ξ⁻¹ := by rw [twist_inv hx]
    _ = ν * (x * ξ⁻¹) := by group

theorem twist_of_comm {G : Type*} [Group G] {c ξ ν : G} (hc : c * ν = ν * c)
    (hξ : ξ * ν = ν⁻¹ * ξ) : c * ξ * ν = ν⁻¹ * (c * ξ) := by
  have e : ν⁻¹ * c = c * ν⁻¹ := by
    calc ν⁻¹ * c = ν⁻¹ * (c * ν) * ν⁻¹ := by group
      _ = ν⁻¹ * (ν * c) * ν⁻¹ := by rw [hc]
      _ = c * ν⁻¹ := by group
  calc c * ξ * ν = c * (ξ * ν) := by group
    _ = c * (ν⁻¹ * ξ) := by rw [hξ]
    _ = (c * ν⁻¹) * ξ := by group
    _ = (ν⁻¹ * c) * ξ := by rw [e]
    _ = ν⁻¹ * (c * ξ) := by group

theorem pr_ppow {p : Nat} {g : Equiv.Perm (Fin 820)} (hp : PR p g) (e : Nat) :
    PR (KernelCU43Aut.ppow p e) (g ^ e) :=
  Raw.Orb.prep_of_rep (rep_ppow (Raw.Orb.rep_unpack hp) e)

theorem cK_ppow {p : Nat} (hp : cK p = true) : ∀ e, cK (KernelCU43Aut.ppow p e) = true
  | 0 => cK_pidn
  | e + 1 => cK_pc hp (cK_ppow hp e)

theorem sq_iff {y : Nat} {γ : Equiv.Perm (Fin 820)} (hc : cK y = true) (hy : PR y γ) :
    Nat.beq (pc y y) (pidn 820 10) = true ↔ γ * γ = 1 := by
  constructor
  · intro h
    exact pr_eq (pr_pc hy hy) pr_pidn (Nat.eq_of_beq_eq_true h)
  · intro h
    have p := pr_pc hy hy
    rw [h] at p
    rw [canon_eq (cK_pc hc hc) cK_pidn p pr_pidn, Nat.beq_refl]

theorem rep_of_bind {p : Nat} {t : Array Nat} {g : Equiv.Perm (Fin 820)}
    (hb : bindListK 820 10 p t.toList = true) (hp : PR p g) : Rep 820 t g := by
  rw [arr_of_bind hb]
  exact Raw.Orb.rep_unpack hp

theorem comm_of_commK {a b : Nat} {α β : Equiv.Perm (Fin 820)} (ha : PR a α) (hb : PR b β)
    (h : commK a b = true) : α * β = β * α :=
  pr_eq (pr_pc ha hb) (pr_pc hb ha) (Nat.eq_of_beq_eq_true h)

theorem wit_spec {w r k : Nat} {ρ : Equiv.Perm (Fin 820)} (hk : k < 8) (hr : PR r ρ)
    (h : witK w r k = true) : ∃ ω, PR w ω ∧ ω * (tP k)⁻¹ ∈ P ∧ ω * ρ = ρ * ω := by
  unfold witK at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨ω, hω, hωP⟩ := coset_pr hk h1 h2
  exact ⟨ω, hω, hωP, comm_of_commK hω hr h3⟩

theorem centKs_of_wit {r : Array Nat} {ρ w2 w5 : Equiv.Perm (Fin 820)} (hr : Rep 820 r ρ)
    (hw2 : w2 * (tP 2)⁻¹ ∈ P) (hc2 : w2 * ρ = ρ * w2) (hw5 : w5 * (tP 5)⁻¹ ∈ P)
    (hc5 : w5 * ρ = ρ * w5) :
    centKs r = 4 * Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820)))) := by
  have hw7 : w2 * w5 * (tP 7)⁻¹ ∈ P := by
    have e27 : tP 2 * tP 5 = tP 7 := by rw [tP_mul_eq (by norm_num) (by norm_num)]; rfl
    have hN := (mem_normalizer_iff.1 (tP_mem_normalizer 2) (w5 * (tP 5)⁻¹)).1 hw5
    have e : w2 * w5 * (tP 7)⁻¹ = (w2 * (tP 2)⁻¹) * (tP 2 * (w5 * (tP 5)⁻¹) * (tP 2)⁻¹) *
        (tP 2 * tP 5 * (tP 7)⁻¹) := by group
    rw [e, e27, mul_inv_cancel, mul_one]
    exact mul_mem hw2 hN
  have hw0 : (1 : Equiv.Perm (Fin 820)) * (tP 0)⁻¹ ∈ P := by
    rw [tP_zero, inv_one, one_mul]
    exact one_mem _
  have c2 : Commute w2 ρ := hc2
  have c5 : Commute w5 ρ := hc5
  simp only [centKs, vIxL, List.foldl_cons, List.foldl_nil, zero_add]
  rw [count_coset hr, count_coset hr, count_coset hr, count_coset hr,
    card_coset_cent hw0 (Commute.one_left _), card_coset_cent hw2 c2,
    card_coset_cent hw5 c5, card_coset_cent hw7 (c2.mul_left c5)]
  ring

theorem pr_R4 : PR (CU43T 6) (rP 4) := by
  have e : reps[4]! = unpack 820 10 (CU43T 6) := reps_T 4 (by norm_num)
  have h := rep_rP (j := 4) (by norm_num)
  rw [e] at h
  exact Raw.Orb.prep_of_rep h

theorem ord8_iff {y : Nat} {γ : Equiv.Perm (Fin 820)} (hc : cK y = true) (hy : PR y γ)
    (h : ord8K y = true) : γ ^ 8 = 1 ∧ γ ^ 4 ≠ 1 :=
  ord8_facts (r := y) hc hy h

theorem y8_data : ∃ γ, PR (Y8 0) γ ∧ γ ∈ P ∧ γ ^ 8 = 1 ∧ γ ^ 4 ≠ 1 ∧ γ * rP 4 = rP 4 * γ := by
  have h := ks2U7
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨γ, hγ, hγP⟩ := mem_P h1 h2
  exact ⟨γ, hγ, hγP, (ord8_iff h1 hγ h3).1, (ord8_iff h1 hγ h3).2, comm_of_commK hγ pr_R4 h4⟩

theorem u7Check_true : u7Check () = true := by
  obtain ⟨γ, hγ, hγP, h8, h4, hc⟩ := y8_data
  have hr : Rep 820 y8Arr γ := rep_of_bind ks2Bind.1 hγ
  have h := ks2CosU
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨w2, -, hw2, hc2⟩ := wit_spec (by norm_num) pr_R4 h.1
  obtain ⟨w5, -, hw5, hc5⟩ := wit_spec (by norm_num) pr_R4 h.2
  have hR := rep_rP (j := 4) (by norm_num)
  have hcent : centKs reps[4]! = 2880 := by
    rw [centKs_of_wit hR hw2 hc2 hw5 hc5, card_inf_centralizer_rP (by norm_num)]
    simp [repCent]
  have e1 : isInvA 820 y8Arr (invCand 820 y8Arr) = true := isInvA_of_rep hr (rep_invCand hr)
  have e2 : inP y8Arr = true := (inP_iff hr).2 hγP
  have e3 : eqA 820 (powA 820 y8Arr 8) (idA 820) = true := (eqA_iff (rep_powA hr 8) rep_idA).2 h8
  have e4 : eqA 820 (powA 820 y8Arr 4) (idA 820) = false := by
    cases e : eqA 820 (powA 820 y8Arr 4) (idA 820)
    · rfl
    · exact absurd ((eqA_iff (rep_powA hr 4) rep_idA).1 e) h4
  have e5 : eqA 820 (compA 820 y8Arr reps[4]!) (compA 820 reps[4]! y8Arr) = true :=
    (eqA_iff (rep_compA hr hR) (rep_compA hR hr)).2 hc
  unfold u7Check
  rw [hcent, e1, e2, e3, e4, e5]
  rfl

theorem d16_data : ∃ α β, PR (DA 0) α ∧ PR (DB 0) β ∧ α * (tP 5)⁻¹ ∈ P ∧ β * (tP 5)⁻¹ ∈ P ∧
    α ^ 8 = 1 ∧ α ^ 4 ≠ 1 ∧ β * β = 1 ∧ α * (β * α) = β ∧ (∀ j < 8, β ≠ α ^ j) ∧
    commK (DA 0) (V 2) = true ∧ commK (DB 0) (V 2) = true ∧ commK (DA 0) (XI 2) = true ∧
    commK (DB 0) (XI 2) = true := by
  have h := ks2D16
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hd, hm⟩ := h
  unfold d16K at hd
  unfold comm4K at hm
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hd hm
  obtain ⟨ca, cb, ia, ib, o8, sb, rel, nj⟩ := hd
  obtain ⟨α, hα, hαP⟩ := coset_pr (by norm_num) ca ia
  obtain ⟨β, hβ, hβP⟩ := coset_pr (by norm_num) cb ib
  refine ⟨α, β, hα, hβ, hαP, hβP, (ord8_iff ca hα o8).1, (ord8_iff ca hα o8).2,
    (sq_iff cb hβ).1 sb, pr_eq (pr_pc hα (pr_pc hβ hα)) hβ (Nat.eq_of_beq_eq_true rel),
    fun j hj e => ?_, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2⟩
  have hj' := Raw.Orb.allN_iff.1 nj j hj
  have p := pr_ppow hα j
  rw [← e] at p
  rw [canon_eq cb (cK_ppow ca j) hβ p, Nat.beq_refl] at hj'
  exact Bool.false_ne_true hj'

theorem d16Check_true : d16Check () = true := by
  obtain ⟨α, β, hα, hβ, hαP, hβP, h8, h4, hb2, hrel, hne, ca, cb, cax, cbx⟩ := d16_data
  obtain ⟨b0, -, -, b3, -, -, b6, b7, b8⟩ := ks2Bind
  have ra : Rep 820 d16A α := rep_of_bind b7 hα
  have rb : Rep 820 d16B β := rep_of_bind b8 hβ
  have hv : PR (V 2) (rK 7) := pr_of_bind b6 (rep_ks (by norm_num))
  have rv : Rep 820 ks8Reps[7]! (rK 7) := rep_ks (by norm_num)
  have hxi := Raw.Orb.allN_iff.1 ks2Xi 2 (by norm_num)
  unfold xiK at hxi
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at hxi
  obtain ⟨xc, -, xi7, -⟩ := hxi
  obtain ⟨ξ, hξ, -⟩ := coset_pr (by norm_num) xc xi7
  have rx : Rep 820 xiArrs[2]! ξ := rep_of_bind b3 hξ
  have hinv : β * α = α⁻¹ * β := by
    calc β * α = α⁻¹ * (α * (β * α)) := by group
      _ = α⁻¹ * β := by rw [hrel]
  have e1 : isInvA 820 d16A (invCand 820 d16A) = true := isInvA_of_rep ra (rep_invCand ra)
  have e2 : isInvA 820 d16B (invCand 820 d16B) = true := isInvA_of_rep rb (rep_invCand rb)
  have e3 : inP (compA 820 d16A (invCand 820 (tArr 5))) = true :=
    (inP_iff (rep_compA ra (rep_tArr_inv (by norm_num)))).2 hαP
  have e4 : inP (compA 820 d16B (invCand 820 (tArr 5))) = true :=
    (inP_iff (rep_compA rb (rep_tArr_inv (by norm_num)))).2 hβP
  have e5 : eqA 820 (powA 820 d16A 8) (idA 820) = true := (eqA_iff (rep_powA ra 8) rep_idA).2 h8
  have e6 : eqA 820 (powA 820 d16A 4) (idA 820) = false := by
    cases e : eqA 820 (powA 820 d16A 4) (idA 820)
    · rfl
    · exact absurd ((eqA_iff (rep_powA ra 4) rep_idA).1 e) h4
  have e7 : eqA 820 (compA 820 d16B d16B) (idA 820) = true :=
    (eqA_iff (rep_compA rb rb) rep_idA).2 hb2
  have e8 : eqA 820 (compA 820 d16B d16A) (compA 820 (invCand 820 d16A) d16B) = true :=
    (eqA_iff (rep_compA rb ra) (rep_compA (rep_invCand ra) rb)).2 hinv
  have e9 : (List.range 8).all (fun j => !eqA 820 d16B (powA 820 d16A j)) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    cases e : eqA 820 d16B (powA 820 d16A j)
    · rfl
    · exact absurd ((eqA_iff rb (rep_powA ra j)).1 e) (hne j hj')
  have e10 : [ks8Reps[7]!, xiArrs[2]!].all (fun r =>
      eqA 820 (compA 820 d16A r) (compA 820 r d16A) &&
        eqA 820 (compA 820 d16B r) (compA 820 r d16B)) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (eqA_iff (rep_compA ra rv) (rep_compA rv ra)).2 (comm_of_commK hα hv ca)
    · exact (eqA_iff (rep_compA rb rv) (rep_compA rv rb)).2 (comm_of_commK hβ hv cb)
    · exact (eqA_iff (rep_compA ra rx) (rep_compA rx ra)).2 (comm_of_commK hα hξ cax)
    · exact (eqA_iff (rep_compA rb rx) (rep_compA rx rb)).2 (comm_of_commK hβ hξ cbx)
  unfold d16Check
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  rfl

theorem vals {i : Nat} (hi : i < 3) :
    (i = 0 ∧ blkS i = 0 ∧ blkE i = 4 ∧ xS i = 0 ∧ xE i = 4) ∨
      (i = 1 ∧ blkS i = 4 ∧ blkE i = 20 ∧ xS i = 4 ∧ xE i = 12) ∨
        (i = 2 ∧ blkS i = 20 ∧ blkE i = 68 ∧ xS i = 12 ∧ xE i = 24) := by
  interval_cases i
  · exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem list_all {i q : Nat} (hi : i < 3) (h1 : blkS i ≤ q) (h2 : q < blkE i) :
    listK i q = true := by
  interval_cases i
  · have e : blkE 0 = 4 := rfl
    rw [e] at h2
    exact Raw.Orb.allN_iff.1 ks2L0 q h2
  · have s : blkS 1 = 4 := rfl
    have e : blkE 1 = 20 := rfl
    rw [s] at h1
    rw [e] at h2
    have := Raw.Orb.allN_iff.1 ks2L1 (q - 4) (by omega)
    have e' : Nat.add 4 (q - 4) = q := by rw [Nat.add_eq]; omega
    rwa [e'] at this
  · have s : blkS 2 = 20 := rfl
    have e : blkE 2 = 68 := rfl
    rw [s] at h1
    rw [e] at h2
    rcases (by omega : q < 36 ∨ (36 ≤ q ∧ q < 52) ∨ 52 ≤ q) with h | h | h
    · have := Raw.Orb.allN_iff.1 ks2L2 (q - 20) (by omega)
      have e' : Nat.add 20 (q - 20) = q := by rw [Nat.add_eq]; omega
      rwa [e'] at this
    · have := Raw.Orb.allN_iff.1 ks2L3 (q - 36) (by omega)
      have e' : Nat.add 36 (q - 36) = q := by rw [Nat.add_eq]; omega
      rwa [e'] at this
    · have := Raw.Orb.allN_iff.1 ks2L4 (q - 52) (by omega)
      have e' : Nat.add 52 (q - 52) = q := by rw [Nat.add_eq]; omega
      rwa [e'] at this

theorem listK_spec {i q : Nat} (h : listK i q = true) :
    cK (C q) = true ∧ inPK (C q) = true ∧ commK (C q) (V i) = true ∧
      (q + 1 < blkE i → C q < C (q + 1)) := by
  unfold listK at h
  rw [Raw.Orb.strictB_eq] at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun hq => ?_⟩
  rw [Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr hq)] at h4
  exact Nat.blt_eq.mp h4

theorem cG_ex (q : Nat) : ∃ γ : Equiv.Perm (Fin 820),
    (cK (C q) = true ∧ inPK (C q) = true) → PR (C q) γ ∧ γ ∈ P := by
  by_cases h : cK (C q) = true ∧ inPK (C q) = true
  · obtain ⟨γ, hγ, hγP⟩ := mem_P h.1 h.2
    exact ⟨γ, fun _ => ⟨hγ, hγP⟩⟩
  · exact ⟨1, fun h' => absurd h' h⟩

@[expose] noncomputable def cG (q : Nat) : Equiv.Perm (Fin 820) := (cG_ex q).choose

theorem pr_V {i : Nat} (hi : i < 3) : PR (V i) (rK (5 + i)) := by
  obtain ⟨-, -, -, -, b4, b5, b6, -, -⟩ := ks2Bind
  interval_cases i
  · exact pr_of_bind b4 (rep_ks (by norm_num))
  · exact pr_of_bind b5 (rep_ks (by norm_num))
  · exact pr_of_bind b6 (rep_ks (by norm_num))

theorem cG_spec {i q : Nat} (hi : i < 3) (h1 : blkS i ≤ q) (h2 : q < blkE i) :
    PR (C q) (cG q) ∧ cG q ∈ P ∧ cG q * rK (5 + i) = rK (5 + i) * cG q := by
  obtain ⟨c1, c2, c3, -⟩ := listK_spec (list_all hi h1 h2)
  obtain ⟨hp, hP⟩ := (cG_ex q).choose_spec ⟨c1, c2⟩
  exact ⟨hp, hP, comm_of_commK hp (pr_V hi) c3⟩

theorem C_mono {i : Nat} (hi : i < 3) : ∀ a b, blkS i ≤ a → a < b → b < blkE i → C a < C b := by
  intro a b ha hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
    · exact (ih h (by omega)).trans ((listK_spec (list_all hi (by omega) (by omega))).2.2.2 hb)
    · exact (listK_spec (list_all hi ha (by omega))).2.2.2 hb

theorem cG_inj {i a b : Nat} (hi : i < 3) (ha1 : blkS i ≤ a) (ha2 : a < blkE i) (hb1 : blkS i ≤ b)
    (hb2 : b < blkE i) (e : cG a = cG b) : a = b := by
  have pa := (cG_spec hi ha1 ha2).1
  have pb := (cG_spec hi hb1 hb2).1
  rw [e] at pa
  have hc := canon_eq (listK_spec (list_all hi ha1 ha2)).1 (listK_spec (list_all hi hb1 hb2)).1
    pa pb
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd hc (Nat.ne_of_lt (C_mono hi a b ha1 h hb2))
  · exact h
  · exact absurd hc (Nat.ne_of_gt (C_mono hi b a hb1 h ha2))

theorem card_CP {i : Nat} (hi : i < 3) :
    Nat.card ↥(P ⊓ centralizer ({rK (5 + i)} : Set (Equiv.Perm (Fin 820)))) = blkE i - blkS i := by
  have hd := card_delta hi
  rw [Nat.add_comm 5 i, hd]
  interval_cases i
  · rw [card_two]; rfl
  · rw [card_cent3]; rfl
  · rw [card_cent4]; rfl

theorem listed {i : Nat} (hi : i < 3) {c : Equiv.Perm (Fin 820)} (hc : c ∈ P)
    (hcv : c * rK (5 + i) = rK (5 + i) * c) : ∃ q, blkS i ≤ q ∧ q < blkE i ∧ cG q = c := by
  classical
  let F : Finset (Equiv.Perm (Fin 820)) := (Finset.Ico (blkS i) (blkE i)).image cG
  have hF : F.card = blkE i - blkS i := by
    rw [Finset.card_image_of_injOn, Nat.card_Ico]
    intro a ha b hb e
    obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.1 ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.1 hb
    exact cG_inj hi ha1 ha2 hb1 hb2 e
  let S : Set (Equiv.Perm (Fin 820)) := ↑(P ⊓ centralizer ({rK (5 + i)} : Set (Equiv.Perm (Fin 820))))
  have hsub : (↑F : Set (Equiv.Perm (Fin 820))) ⊆ S := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hq1, hq2⟩ := Finset.mem_Ico.1 hq
    obtain ⟨-, hP, hcm⟩ := cG_spec hi hq1 hq2
    exact mem_inf.2 ⟨hP, mem_centralizer_singleton_iff.2 hcm⟩
  have hS : Nat.card ↥(P ⊓ centralizer ({rK (5 + i)} : Set (Equiv.Perm (Fin 820)))) = S.ncard :=
    Nat.card_coe_set_eq S
  have hcard : S.ncard ≤ (↑F : Set (Equiv.Perm (Fin 820))).ncard := by
    rw [Set.ncard_coe_finset, hF, ← card_CP hi, hS]
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  have hcS : c ∈ S := mem_inf.2 ⟨hc, mem_centralizer_singleton_iff.2 hcv⟩
  rw [← heq] at hcS
  obtain ⟨q, hq, e⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hcS)
  obtain ⟨hq1, hq2⟩ := Finset.mem_Ico.1 hq
  exact ⟨q, hq1, hq2, e⟩

theorem xi_ex (i : Nat) : ∃ ξ : Equiv.Perm (Fin 820), i < 3 →
    PR (XI i) ξ ∧ ξ * (tP 7)⁻¹ ∈ P ∧ ξ * ξ = 1 ∧ rK (5 + i) * (ξ * rK (5 + i)) = ξ := by
  by_cases hi : i < 3
  · have h := Raw.Orb.allN_iff.1 ks2Xi i hi
    unfold xiK at h
    simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨ξ, hξ, hξP⟩ := coset_pr (by norm_num) h1 h3
    refine ⟨ξ, fun _ => ⟨hξ, hξP, (sq_iff h1 hξ).1 h2, ?_⟩⟩
    exact pr_eq (pr_pc (pr_V hi) (pr_pc hξ (pr_V hi))) hξ (Nat.eq_of_beq_eq_true h4)
  · exact ⟨1, fun h => absurd h hi⟩

@[expose] noncomputable def xG (i : Nat) : Equiv.Perm (Fin 820) := (xi_ex i).choose

theorem xG_spec {i : Nat} (hi : i < 3) :
    PR (XI i) (xG i) ∧ xG i * (tP 7)⁻¹ ∈ P ∧ xG i * xG i = 1 ∧
      rK (5 + i) * (xG i * rK (5 + i)) = xG i :=
  (xi_ex i).choose_spec hi

theorem xG_twist {i : Nat} (hi : i < 3) :
    xG i * rK (5 + i) = (rK (5 + i))⁻¹ * xG i := by
  have h := (xG_spec hi).2.2.2
  calc xG i * rK (5 + i) = (rK (5 + i))⁻¹ * (rK (5 + i) * (xG i * rK (5 + i))) := by group
    _ = (rK (5 + i))⁻¹ * xG i := by rw [h]

theorem invT_iff {i q : Nat} (hi : i < 3) (h1 : blkS i ≤ q) (h2 : q < blkE i) :
    invT i q = true ↔ cG q * xG i * (cG q * xG i) = 1 := by
  have hc := (listK_spec (list_all hi h1 h2)).1
  have hx := (xi_ex i).choose_spec hi
  have hy : PR (pc (C q) (XI i)) (cG q * xG i) := pr_pc (cG_spec hi h1 h2).1 hx.1
  have hxc : cK (XI i) = true := by
    have h := Raw.Orb.allN_iff.1 ks2Xi i hi
    unfold xiK at h
    simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    exact h.1
  unfold invT
  rw [Raw.Orb.strictB_eq]
  exact sq_iff (cK_pc hc hxc) hy

theorem wK_spec {i k : Nat} (hi : i < 3) (hk : isV k = true) :
    ∃ ω, PR (wK i k) ω ∧ ω ∈ Kv ∧ ω * rK (5 + i) = rK (5 + i) * ω := by
  have hv := pr_V hi
  have hc := Raw.Orb.allN_iff.1 ks2Cos i hi
  rw [Raw.Orb.strictB_eq] at hc
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hc
  obtain ⟨h7, h2, h5⟩ := hc
  unfold isV at hk
  simp only [Raw.Orb.bIf_eq] at hk
  rcases (by
    by_cases e0 : Nat.beq k 0 = true
    · exact Or.inl (Nat.eq_of_beq_eq_true e0)
    · rw [if_neg e0] at hk
      by_cases e2 : Nat.beq k 2 = true
      · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true e2))
      · rw [if_neg e2] at hk
        by_cases e5 : Nat.beq k 5 = true
        · exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true e5)))
        · rw [if_neg e5] at hk
          exact Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true hk))) :
      k = 0 ∨ k = 2 ∨ k = 5 ∨ k = 7) with rfl | rfl | rfl | rfl
  · refine ⟨1, ?_, one_mem _, by group⟩
    have e : wK i 0 = pidn 820 10 := rfl
    rw [e]
    exact pr_pidn
  · obtain ⟨ω, hω, hωP, hωc⟩ := wit_spec (by norm_num) hv h2
    exact ⟨ω, hω, mem_Kv_of (by norm_num) (Or.inr (Or.inl rfl)) hωP, hωc⟩
  · obtain ⟨ω, hω, hωP, hωc⟩ := wit_spec (by norm_num) hv h5
    exact ⟨ω, hω, mem_Kv_of (by norm_num) (Or.inr (Or.inr (Or.inl rfl))) hωP, hωc⟩
  · obtain ⟨ω, hω, hωP, -⟩ := wit_spec (by norm_num) hv h7
    have e : ω = rK (5 + i) := pr_eq hω hv rfl
    subst e
    exact ⟨_, hv, mem_Kv_of (by norm_num) (Or.inr (Or.inr (Or.inr rfl))) hωP, rfl⟩

theorem pairOf_eq {i r : Nat} (hi : i < 3) (h1 : xS i ≤ r) (h2 : r < xE i) : pairOf r = i := by
  have f4 : r < 4 → pairOf r = 0 := fun h => by
    unfold pairOf
    rw [Nat.blt_eq.mpr h]
  have g4 : 4 ≤ r → Nat.blt r 4 = false := fun h =>
    Bool.eq_false_iff.2 fun e => absurd (Nat.blt_eq.mp e) (by omega)
  rcases vals hi with ⟨rfl, -, -, s, e⟩ | ⟨rfl, -, -, s, e⟩ | ⟨rfl, -, -, s, e⟩ <;>
    rw [s] at h1 <;> rw [e] at h2
  · exact f4 h2
  · unfold pairOf
    rw [g4 h1, Nat.blt_eq.mpr h2]
  · unfold pairOf
    rw [g4 (by omega), Bool.eq_false_iff.2 fun e => absurd (Nat.blt_eq.mp e) (by omega)]

theorem xK_spec {i : Nat} (hi : i < 3) :
    xCnt i = xE i - xS i ∧ ∀ r, xS i ≤ r → r < xE i →
      blkS i ≤ XL r ∧ XL r < blkE i ∧ invT i (XL r) = true ∧
        (r + 1 < xE i → XL r < XL (r + 1)) := by
  have h := Raw.Orb.allN_iff.1 ks2X i hi
  unfold xK at h
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun r hr1 hr2 => ?_⟩
  have h3 := Raw.Orb.allN_iff.1 h2 (r - xS i) (by rw [Nat.sub_eq]; omega)
  have e : Nat.add (xS i) (r - xS i) = r := by simp only [Nat.add_eq]; omega
  rw [Raw.Orb.strictB_eq, e, Raw.Orb.strictB_eq] at h3
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h3
  obtain ⟨a1, a2, a3, a4⟩ := h3
  refine ⟨Nat.le_of_ble_eq_true a1, Nat.blt_eq.mp a2, a3, fun hr => ?_⟩
  rw [Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr hr)] at a4
  exact Nat.blt_eq.mp a4

theorem XL_mono {i : Nat} (hi : i < 3) : ∀ a b, xS i ≤ a → a < b → b < xE i → XL a < XL b := by
  intro a b ha hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
    · exact (ih h (by omega)).trans (((xK_spec hi).2 b (by omega) (by omega)).2.2.2 hb)
    · exact ((xK_spec hi).2 a ha (by omega)).2.2.2 hb

@[expose] noncomputable def FX (i : Nat) : Finset Nat :=
  (Finset.Ico (blkS i) (blkE i)).filter fun q => invT i q = true

theorem card_FX {i : Nat} (hi : i < 3) : (FX i).card = xE i - xS i := by
  classical
  rw [← (xK_spec hi).1]
  unfold xCnt
  rw [foldUp_count (fun d => invT i (Nat.add (blkS i) d)) (Nat.sub (blkE i) (blkS i))]
  simp only [Nat.sub_eq, Nat.add_eq]
  unfold FX
  symm
  refine Finset.card_bij (fun d _ => blkS i + d) ?_ ?_ ?_
  · intro d hd
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hd
    have := Finset.mem_range.1 h1
    exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, by omega⟩, h2⟩
  · intro a _ b _ e
    omega
  · intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq
    obtain ⟨h3, h4⟩ := Finset.mem_Ico.1 h1
    have e : blkS i + (q - blkS i) = q := by omega
    refine ⟨q - blkS i, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩, e⟩
    rw [e]
    exact h2

theorem XL_listed {i q : Nat} (hi : i < 3) (hq : q ∈ FX i) : ∃ r, xS i ≤ r ∧ r < xE i ∧ XL r = q := by
  classical
  let G : Finset Nat := (Finset.Ico (xS i) (xE i)).image XL
  have hG : G.card = xE i - xS i := by
    rw [Finset.card_image_of_injOn, Nat.card_Ico]
    intro a ha b hb e
    obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.1 ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.1 hb
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd e (Nat.ne_of_lt (XL_mono hi a b ha1 h hb2))
    · exact h
    · exact absurd e (Nat.ne_of_gt (XL_mono hi b a hb1 h ha2))
  have hsub : G ⊆ FX i := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.1 hr
    obtain ⟨a1, a2, a3, -⟩ := (xK_spec hi).2 r hr1 hr2
    exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨a1, a2⟩, a3⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hG, card_FX hi])
  rw [← heq] at hq
  obtain ⟨r, hr, e⟩ := Finset.mem_image.1 hq
  obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.1 hr
  exact ⟨r, hr1, hr2, e⟩

@[expose] def X7 (ν : Equiv.Perm (Fin 820)) : Set (Equiv.Perm (Fin 820)) :=
  {x | x * (tP 7)⁻¹ ∈ P ∧ x * x = 1 ∧ x * ν = ν⁻¹ * x}

theorem card_X7 {i : Nat} (hi : i < 3) : Nat.card ↥(X7 (rK (5 + i))) = xE i - xS i := by
  classical
  have hξ := xG_spec hi
  have hξt := xG_twist hi
  rw [← card_FX hi, ← Nat.card_eq_finsetCard]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨cG q.1 * xG i, ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 q.2
    obtain ⟨h3, h4⟩ := Finset.mem_Ico.1 h1
    obtain ⟨-, hP, hcm⟩ := cG_spec hi h3 h4
    refine ⟨?_, (invT_iff hi h3 h4).1 h2, twist_of_comm hcm hξt⟩
    rw [mul_assoc]
    exact mul_mem hP hξ.2.1
  · intro a b e
    have e1 : cG a.1 * xG i = cG b.1 * xG i := congrArg Subtype.val e
    obtain ⟨ha1, -⟩ := Finset.mem_filter.1 a.2
    obtain ⟨hb1, -⟩ := Finset.mem_filter.1 b.2
    obtain ⟨ha2, ha3⟩ := Finset.mem_Ico.1 ha1
    obtain ⟨hb2, hb3⟩ := Finset.mem_Ico.1 hb1
    exact Subtype.ext (cG_inj hi ha2 ha3 hb2 hb3 (mul_right_cancel e1))
  · rintro ⟨x, hx1, hx2, hx3⟩
    have hcP : x * (xG i)⁻¹ ∈ P := by
      have e : x * (xG i)⁻¹ = (x * (tP 7)⁻¹) * (xG i * (tP 7)⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem hx1 (inv_mem hξ.2.1)
    obtain ⟨q, hq1, hq2, hq⟩ := listed hi hcP (comm_of_twists hx3 hξt)
    have hqx : cG q * xG i = x := by rw [hq]; group
    refine ⟨⟨q, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hq1, hq2⟩, ?_⟩⟩, Subtype.ext hqx⟩
    rw [invT_iff hi hq1 hq2, hqx]
    exact hx2

theorem orbit_X7 {i : Nat} (hi : i < 3) (x : Equiv.Perm (Fin 820)) :
    (∃ h ∈ Kv ⊓ centralizer ({rK (5 + i)} : Set (Equiv.Perm (Fin 820))), x = h * xG i * h⁻¹) ↔
      x ∈ X7 (rK (5 + i)) := by
  have hξ := xG_spec hi
  have hξt := xG_twist hi
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hK, hc⟩ := mem_inf.1 hh
    have hc' : h * rK (5 + i) = rK (5 + i) * h := mem_centralizer_singleton_iff.1 hc
    refine ⟨conj_coset (by norm_num) (Or.inr (Or.inr (Or.inr rfl))) hξ.2.1 hK, ?_, ?_⟩
    · calc h * xG i * h⁻¹ * (h * xG i * h⁻¹) = h * (xG i * xG i) * h⁻¹ := by group
        _ = 1 := by rw [hξ.2.2.1]; group
    · have hi1 : h⁻¹ * rK (5 + i) = rK (5 + i) * h⁻¹ := by
        calc h⁻¹ * rK (5 + i) = h⁻¹ * (rK (5 + i) * h) * h⁻¹ := by group
          _ = h⁻¹ * (h * rK (5 + i)) * h⁻¹ := by rw [hc']
          _ = rK (5 + i) * h⁻¹ := by group
      have hi2 : h * (rK (5 + i))⁻¹ = (rK (5 + i))⁻¹ * h := by
        calc h * (rK (5 + i))⁻¹ = (rK (5 + i))⁻¹ * (rK (5 + i) * h) * (rK (5 + i))⁻¹ := by group
          _ = (rK (5 + i))⁻¹ * (h * rK (5 + i)) * (rK (5 + i))⁻¹ := by rw [hc']
          _ = (rK (5 + i))⁻¹ * h := by group
      calc h * xG i * h⁻¹ * rK (5 + i) = h * xG i * (h⁻¹ * rK (5 + i)) := by group
        _ = h * xG i * (rK (5 + i) * h⁻¹) := by rw [hi1]
        _ = h * (xG i * rK (5 + i)) * h⁻¹ := by group
        _ = h * ((rK (5 + i))⁻¹ * xG i) * h⁻¹ := by rw [hξt]
        _ = (h * (rK (5 + i))⁻¹) * xG i * h⁻¹ := by group
        _ = ((rK (5 + i))⁻¹ * h) * xG i * h⁻¹ := by rw [hi2]
        _ = (rK (5 + i))⁻¹ * (h * xG i * h⁻¹) := by group
  · rintro ⟨hx1, hx2, hx3⟩
    have hcP : x * (xG i)⁻¹ ∈ P := by
      have e : x * (xG i)⁻¹ = (x * (tP 7)⁻¹) * (xG i * (tP 7)⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem hx1 (inv_mem hξ.2.1)
    obtain ⟨q, hq1, hq2, hq⟩ := listed hi hcP (comm_of_twists hx3 hξt)
    have hqx : cG q * xG i = x := by rw [hq]; group
    have hqF : q ∈ FX i := by
      refine Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hq1, hq2⟩, ?_⟩
      rw [invT_iff hi hq1 hq2, hqx]
      exact hx2
    obtain ⟨r, hr1, hr2, hrq⟩ := XL_listed hi hqF
    have ho := Raw.Orb.allN_iff.1 ks2Orb r (by
      rcases vals hi with ⟨-, -, -, -, e⟩ | ⟨-, -, -, -, e⟩ | ⟨-, -, -, -, e⟩ <;> rw [e] at hr2 <;>
        omega)
    unfold orbK at ho
    rw [pairOf_eq hi hr1 hr2] at ho
    unfold orbW at ho
    rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq] at ho
    simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at ho
    obtain ⟨o1, o2, o3, o4⟩ := ho
    obtain ⟨ω, hω, hωK, hωc⟩ := wK_spec hi o3
    have o1' := Nat.le_of_ble_eq_true o1
    have o2' := Nat.blt_eq.mp o2
    obtain ⟨hcq, hcP', hcc⟩ := cG_spec hi o1' o2'
    have hh : PR (pc (C (OQ r)) (wK i (OK r))) (cG (OQ r) * ω) := pr_pc hcq hω
    have hxl := (cG_spec (q := XL r) hi (by rw [hrq]; exact hq1) (by rw [hrq]; exact hq2)).1
    have e := pr_eq (pr_pc hh hξ.1) (pr_pc (pr_pc hxl hξ.1) hh) (Nat.eq_of_beq_eq_true o4)
    rw [hrq, hqx] at e
    refine ⟨cG (OQ r) * ω, mem_inf.2 ⟨mul_mem (P_le_Kv hcP') hωK,
      mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
    · calc cG (OQ r) * ω * rK (5 + i) = cG (OQ r) * (ω * rK (5 + i)) := by group
        _ = cG (OQ r) * (rK (5 + i) * ω) := by rw [hωc]
        _ = (cG (OQ r) * rK (5 + i)) * ω := by group
        _ = (rK (5 + i) * cG (OQ r)) * ω := by rw [hcc]
        _ = rK (5 + i) * (cG (OQ r) * ω) := by group
    · calc x = x * (cG (OQ r) * ω) * (cG (OQ r) * ω)⁻¹ := by group
        _ = cG (OQ r) * ω * xG i * (cG (OQ r) * ω)⁻¹ := by rw [← e]

theorem invRelW_iff' {k : ℕ} {v vi : Array ℕ} {V W : Equiv.Perm (Fin 820)} (hv : Rep 820 v V)
    (hvi : Rep 820 vi W) {w : List (Array ℕ)} {g : Equiv.Perm (Fin 820)} (hw : RepW 820 w g) :
    invRelW (tArr k) v vi w = true ↔
      (g * tP k) * (g * tP k) = 1 ∧ (g * tP k) * V = W * (g * tP k) := by
  have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
  unfold invRelW
  rw [Bool.and_eq_true]
  exact and_congr (allLt_sq_iff hH) (allLt_twist_iff hH hv hvi)

theorem count_X7 {i : Nat} (hi : i < 3) :
    countW (invRelW (tArr 7) ks8Reps[5 + i]! (invCand 820 ks8Reps[5 + i]!)) blocks [] =
      pairNum[i]! := by
  classical
  have hv := rep_ks (j := 5 + i) (by omega)
  have hvi : Rep 820 (invCand 820 ks8Reps[5 + i]!) (rK (5 + i))⁻¹ :=
    rep_inv_of_isInvA hv (isInvA_of_rep hv (rep_invCand hv))
  rw [← card_eq_countW_P (f := invRelW (tArr 7) ks8Reps[5 + i]! (invCand 820 ks8Reps[5 + i]!))
    (Pr := fun g => (g * tP 7) * (g * tP 7) = 1 ∧ (g * tP 7) * rK (5 + i) = (rK (5 + i))⁻¹ * (g * tP 7))
    (fun w g hw _ => invRelW_iff' hv hvi hw)]
  have e : pairNum[i]! = xE i - xS i := by
    rcases vals hi with ⟨rfl, -, -, s, e⟩ | ⟨rfl, -, -, s, e⟩ | ⟨rfl, -, -, s, e⟩ <;> rw [s, e] <;> rfl
  rw [e, ← card_X7 hi]
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : Equiv.Perm (Fin 820)) * tP 7, by
        rw [mul_inv_cancel_right]; exact g.1.2, g.2.1, g.2.2⟩
      invFun := fun x => ⟨⟨x.1 * (tP 7)⁻¹, x.2.1⟩, by
        rw [inv_mul_cancel_right]; exact ⟨x.2.2.1, x.2.2.2⟩⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply Subtype.ext
        change (g.1 : Equiv.Perm (Fin 820)) * tP 7 * (tP 7)⁻¹ = g.1
        group
      right_inv := fun x => by
        apply Subtype.ext
        change x.1 * (tP 7)⁻¹ * tP 7 = x.1
        group }

theorem centKs2_eq {v ξ : Array ℕ} {V X : Equiv.Perm (Fin 820)} (hv : Rep 820 v V)
    (hξ : Rep 820 ξ X) :
    centKs2 v ξ = Nat.card ↥(Kv ⊓ centralizer ({V} : Set (Equiv.Perm (Fin 820))) ⊓
      centralizer ({X} : Set (Equiv.Perm (Fin 820)))) := by
  classical
  have e0 : Nat.card ↥(Kv ⊓ centralizer ({V} : Set (Equiv.Perm (Fin 820))) ⊓
      centralizer ({X} : Set (Equiv.Perm (Fin 820)))) =
      Nat.card {x : ↥Kv // (x : Equiv.Perm (Fin 820)) * V = V * x ∧
        (x : Equiv.Perm (Fin 820)) * X = X * x} :=
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, (mem_inf.1 (mem_inf.1 x.2).1).1⟩,
          mem_centralizer_singleton_iff.1 (mem_inf.1 (mem_inf.1 x.2).1).2,
          mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2⟩
        invFun := fun y => ⟨y.1.1, mem_inf.2 ⟨mem_inf.2 ⟨y.1.2,
          mem_centralizer_singleton_iff.2 y.2.1⟩, mem_centralizer_singleton_iff.2 y.2.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e0, card_Kv_pred (fun x => x * V = V * x ∧ x * X = X * x)]
  have h : ∀ k, k < 8 → Nat.card {g : ↥P // (g : Equiv.Perm (Fin 820)) * tP k * V =
      V * ((g : Equiv.Perm (Fin 820)) * tP k) ∧ (g : Equiv.Perm (Fin 820)) * tP k * X =
        X * ((g : Equiv.Perm (Fin 820)) * tP k)} =
      countW (commW (tArr k) [v, ξ]) blocks [] := by
    intro k hk
    rw [card_eq_countW_P (f := commW (tArr k) [v, ξ])
      (Pr := fun g => g * tP k * V = V * (g * tP k) ∧ g * tP k * X = X * (g * tP k))]
    intro w g hw _
    have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
    simp only [commW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact and_congr (allLt_comm_iff hH hv) (allLt_comm_iff hH hξ)
  rw [h 0 (by norm_num), h 2 (by norm_num), h 5 (by norm_num), h 7 (by norm_num)]
  simp [centKs2, vIxL]

theorem cent_pair {i : Nat} (hi : i < 3) : centKs2 ks8Reps[5 + i]! xiArrs[i]! = pairCent[i]! := by
  have hv := rep_ks (j := 5 + i) (by omega)
  obtain ⟨-, b1, b2, b3, -, -, -, -, -⟩ := ks2Bind
  have hx : Rep 820 xiArrs[i]! (xG i) := by
    have p := (xG_spec hi).1
    interval_cases i
    · exact rep_of_bind b1 p
    · exact rep_of_bind b2 p
    · exact rep_of_bind b3 p
  rw [centKs2_eq hv hx]
  set H := Kv ⊓ centralizer ({rK (5 + i)} : Set (Equiv.Perm (Fin 820))) with hH
  have h1 := card_orbit_subgroup_mul H (xG i)
  have e1 : Nat.card {x : Equiv.Perm (Fin 820) // ∃ h ∈ H, x = h * xG i * h⁻¹} =
      Nat.card ↥(X7 (rK (5 + i))) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => orbit_X7 hi x)
  have e2 : Nat.card ↥H = 4 * (blkE i - blkS i) := by
    rw [← card_CP hi, ← card_centKv' (by omega)]
    rfl
  rw [e1, card_X7 hi, e2] at h1
  rcases vals hi with ⟨rfl, s, e, xs, xe⟩ | ⟨rfl, s, e, xs, xe⟩ | ⟨rfl, s, e, xs, xe⟩ <;>
    rw [s, e, xs, xe] at h1
  · have p : pairCent[0]! = 4 := rfl
    rw [p]
    omega
  · have p : pairCent[1]! = 8 := rfl
    rw [p]
    omega
  · have p : pairCent[2]! = 16 := rfl
    rw [p]
    omega

theorem pairCheck_true : pairCheck () = true := by
  simp only [pairCheck, List.all_eq_true, List.mem_range]
  intro i hi
  have hv := rep_ks (j := 5 + i) (by omega)
  obtain ⟨-, b1, b2, b3, -, -, -, -, -⟩ := ks2Bind
  obtain ⟨hp, hP, h2, h3⟩ := xG_spec hi
  have hx : Rep 820 xiArrs[i]! (xG i) := by
    interval_cases i
    · exact rep_of_bind b1 hp
    · exact rep_of_bind b2 hp
    · exact rep_of_bind b3 hp
  have hvi : Rep 820 (invCand 820 ks8Reps[5 + i]!) (rK (5 + i))⁻¹ := rep_invCand hv
  have e1 : isInvA 820 xiArrs[i]! (invCand 820 xiArrs[i]!) = true := isInvA_of_rep hx (rep_invCand hx)
  have e2 : eqA 820 (compA 820 xiArrs[i]! xiArrs[i]!) (idA 820) = true :=
    (eqA_iff (rep_compA hx hx) rep_idA).2 h2
  have e3 : inP (compA 820 xiArrs[i]! (invCand 820 (tArr 7))) = true :=
    (inP_iff (rep_compA hx (rep_tArr_inv (by norm_num)))).2 hP
  have e4 : eqA 820 (compA 820 xiArrs[i]! ks8Reps[5 + i]!)
      (compA 820 (invCand 820 ks8Reps[5 + i]!) xiArrs[i]!) = true :=
    (eqA_iff (rep_compA hx hv) (rep_compA hvi hx)).2 (xG_twist hi)
  rw [e1, e2, e3, e4, count_X7 hi, cent_pair hi]
  simp

end CertificateChecks.KernelKs2.G

end
