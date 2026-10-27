module

public import Certificates.Kernel.Sporadic.Fi22.AutH25290K
public import Certificates.Kernel.Sporadic.Fi22.Five8124G
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueLin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.AH25

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fv8124
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem isP_eq : isP = Fv8124.isP := rfl

theorem idP_eq : idP = Fv8124.idP := rfl

theorem bitB_eq (m i : ℕ) : bitB m i = m.testBit i := by
  change Nat.blt 0 (m &&& (1 <<< i)) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow]
  cases m.testBit i
  · rw [Bool.toNat_false, Nat.zero_mul]
    rfl
  · simp only [Bool.toNat_true, Nat.one_mul]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos i)

theorem basisOK_spec {b : ℕ} (h : basisOK b = true) :
    isP b = true ∧ Nat.beq (Fi22X.c b b) idP = true ∧ Fi22X.siftP b = true := by
  rw [basisOK.eq_1, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem injOK_spec {Bf : ℕ → ℕ} {Wn m : ℕ} (h : injOK Bf Wn m = true) :
    wl Wn (ptL Bf m L10 0) = m :=
  Nat.eq_of_beq_eq_true (by rw [injOK.eq_1] at h; exact h)

theorem covOK_spec {Bf : ℕ → ℕ} {Wn q : ℕ} (h : covOK Bf Wn q = true) :
    (wl Wn q < 1024 ∧ ptL Bf (wl Wn q) L10 0 = q) ∨
      (0 < wl Wn q - 1024 ∧ wl Wn q - 1024 < 1024 ∧ ptL Bf (wl Wn q - 1024) L10 q = q) := by
  rw [covOK.eq_1, Fv8124.strictB_eq] at h
  generalize wl Wn q = l at h ⊢
  cases hl : Nat.blt l 1024
  · rw [hl] at h
    change strictB (Nat.sub l 1024) _ = true at h
    rw [Fv8124.strictB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    exact Or.inr ⟨Nat.blt_eq.mp h.1.1, Nat.blt_eq.mp h.1.2, Nat.eq_of_beq_eq_true h.2⟩
  · rw [hl] at h
    exact Or.inl ⟨Nat.blt_eq.mp hl, Nat.eq_of_beq_eq_true h⟩

theorem baseOK_spec {Bf R : ℕ → ℕ} {Z Tm j : ℕ} (h : baseOK Bf R Z Tm j = true) :
    R j = Fi22X.c (phL Bf (tl Tm j) L10) (Fi22X.c Z (phL Bf (tl Tm j) L10)) := by
  rw [baseOK.eq_1, Fv8124.strictB_eq] at h
  exact Nat.eq_of_beq_eq_true h

theorem ruleOK_spec {R : ℕ → ℕ} {Tr r : ℕ} (h : ruleOK R Tr r = true) :
    tl Tr (2 * r) < 7 + r ∧ tl Tr (2 * r + 1) < 7 + r ∧
      R (7 + r) = Fi22X.c (R (tl Tr (2 * r))) (R (tl Tr (2 * r + 1))) := by
  rw [ruleOK.eq_1, Fv8124.strictB_eq, Fv8124.strictB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1.1, Nat.blt_eq.mp h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem end_spec {R : ℕ → ℕ} {e0 e1 n F0 F1 : ℕ}
    (h : (Nat.blt e0 (Nat.add 7 n) && Nat.blt e1 (Nat.add 7 n) && Nat.beq (R e0) F0 &&
      Nat.beq (R e1) F1) = true) : e0 < 7 + n ∧ e1 < 7 + n ∧ R e0 = F0 ∧ R e1 = F1 := by
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1.1.1, Nat.blt_eq.mp h.1.1.2, Nat.eq_of_beq_eq_true h.1.2,
    Nat.eq_of_beq_eq_true h.2⟩

section Mono

variable {Bf : ℕ → ℕ} (hB : ∀ i < 10, PP 3510 12 (Bf i))
include hB

theorem pt_eq (m : ℕ) : ∀ l : List ℕ, (∀ i ∈ l, i < 10) → ∀ x : Fin 3510,
    (((phiL (fun i => pe (Bf i)) m l) x : Fin 3510) : ℕ) = ptL Bf m l x
  | [], _, x => rfl
  | i :: l, hl, x => by
    have ih := pt_eq m l (fun k hk => hl k (List.mem_cons_of_mem _ hk)) x
    have e : ptL Bf m (i :: l) x =
        Bool.rec (motive := fun _ => ℕ) (ptL Bf m l x) (ev (Bf i) (ptL Bf m l x)) (bitB m i) :=
      rfl
    rw [phiL_cons, e, bitB_eq]
    cases m.testBit i
    · exact ih
    · rw [if_pos rfl, Equiv.Perm.mul_apply, pe_apply (hB i (hl i List.mem_cons_self)), ← ih]
      rfl

theorem ph_eq (m : ℕ) : ∀ l : List ℕ, (∀ i ∈ l, i < 10) →
    PP 3510 12 (phL Bf m l) ∧ pe (phL Bf m l) = phiL (fun i => pe (Bf i)) m l
  | [], _ => ⟨PP_id, pe_id⟩
  | i :: l, hl => by
    have ih := ph_eq m l fun k hk => hl k (List.mem_cons_of_mem _ hk)
    have e : phL Bf m (i :: l) =
        Bool.rec (motive := fun _ => ℕ) (phL Bf m l) (Fi22X.c (Bf i) (phL Bf m l)) (bitB m i) :=
      rfl
    rw [phiL_cons, e, bitB_eq]
    cases m.testBit i
    · exact ih
    · have hi := hB i (hl i List.mem_cons_self)
      refine ⟨PP_c hi ih.1, ?_⟩
      rw [if_pos rfl, pe_c hi ih.1, ih.2]

end Mono

theorem range_eq : List.range 10 = L10 := by
  rw [L10]
  decide

theorem L10_lt : ∀ i ∈ L10, i < 10 := by
  rw [← range_eq]
  exact fun _ hi => List.mem_range.1 hi

@[expose] noncomputable def b (i : ℕ) : Equiv.Perm (Fin 3510) := pe (AH25B i)

theorem basis {i : ℕ} (hi : i < 10) :
    PP 3510 12 (AH25B i) ∧ b i * b i = 1 ∧ Fi22X.siftP (AH25B i) = true := by
  obtain ⟨h1, h2, h3⟩ := basisOK_spec (allN_spec' okB hi)
  have hp : PP 3510 12 (AH25B i) := PP_of_isP (isP_eq ▸ h1)
  refine ⟨hp, ?_, h3⟩
  rw [b, ← pe_c hp hp, Nat.eq_of_beq_eq_true h2, idP_eq, pe_id]

theorem hPP : ∀ i < 10, PP 3510 12 (AH25B i) := fun _ hi => (basis hi).1

theorem b_sq : ∀ i < 10, b i * b i = 1 := fun _ hi => (basis hi).2.1

theorem b_mem {i : ℕ} (hi : i < 10) :
    b i ∈ fi22P :=
  (mem_P (hPP i hi)).2 (basis hi).2.2

theorem b_comm_lt {i j : ℕ} (hi : i < 10) (hj : j < i) : b i * b j = b j * b i := by
  have h := allN_spec' (allN_spec' okC hi) hj
  rw [b, b, ← pe_c (hPP i hi) (hPP j (by omega)), ← pe_c (hPP j (by omega)) (hPP i hi),
    Nat.eq_of_beq_eq_true h]

theorem b_comm : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i := by
  intro i hi j hj
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · exact (b_comm_lt hj h).symm
  · rfl
  · exact b_comm_lt hi h

@[expose] noncomputable def N : Subgroup (Equiv.Perm (Fin 3510)) := Subgroup.closure (b '' Set.Iio 10)

theorem phi_eq (m : ℕ) : phi b m = phiL b m L10 := by
  rw [phi, range_eq]

theorem phi_apply (m : ℕ) (x : Fin 3510) : (((phi b m) x : Fin 3510) : ℕ) = ptL AH25B m L10 x := by
  rw [phi_eq]
  exact pt_eq hPP m L10 L10_lt x

theorem phi_zero_inj {m m' : ℕ} (hm : m < 1024) (hm' : m' < 1024)
    (h : (phi b m) 0 = (phi b m') 0) : m = m' := by
  have e1 := injOK_spec (allN_spec' okInj hm)
  have e2 := injOK_spec (allN_spec' okInj hm')
  have a1 : (((phi b m) 0 : Fin 3510) : ℕ) = ptL AH25B m L10 0 := phi_apply m 0
  have a2 : (((phi b m') 0 : Fin 3510) : ℕ) = ptL AH25B m' L10 0 := phi_apply m' 0
  rw [← a1, h, a2] at e1
  exact e1.symm.trans e2

theorem exists_phi {x : Equiv.Perm (Fin 3510)} (hx : x ∈ N) : ∃ v < 1024, phi b v = x :=
  exists_phi_of_mem_closure b_comm b_sq hx

theorem card_N : Nat.card N = 2 ^ 10 := by
  have hbij : Function.Bijective (fun m : Fin 1024 => (⟨phi b m.val, phi_mem m.val⟩ : N)) := by
    constructor
    · intro m m' h
      exact Fin.ext (phi_zero_inj m.2 m'.2 (congrArg (fun x : N => (x : Equiv.Perm (Fin 3510)) 0) h))
    · intro x
      obtain ⟨m, hm, hx⟩ := exists_phi x.2
      exact ⟨⟨m, hm⟩, Subtype.ext hx⟩
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp

theorem N_reg {v : Equiv.Perm (Fin 3510)} (hv : v ∈ N) (h : v 0 = 0) : v = 1 := by
  obtain ⟨m, hm, rfl⟩ := exists_phi hv
  have h0 : phi b 0 = 1 := phi_zero
  have : m = 0 := phi_zero_inj hm (by norm_num) (by rw [h, h0]; rfl)
  rw [this, h0]

theorem N_uniq (q : Fin 3510) (hq : ∀ v ∈ N, v q = q → v = 1) : ∃ v ∈ N, v 0 = q := by
  rcases covOK_spec (allN_spec' okCov q.2) with ⟨hl, hpt⟩ | ⟨h0, hl, hpt⟩
  · exact ⟨phi b _, phi_mem _, Fin.ext ((phi_apply _ 0).trans hpt)⟩
  · exfalso
    have hfix : (phi b (wl (AH25W 0) q - 1024)) q = q := Fin.ext ((phi_apply _ q).trans hpt)
    have h1 := hq _ (phi_mem _) hfix
    have : wl (AH25W 0) q - 1024 = 0 :=
      phi_zero_inj hl (by norm_num) (by rw [h1, phi_zero])
    omega

theorem pe_E : pe Fi22E2073.E = fi22OuterZ := by
  have h := rep_fi22OuterZ
  rw [Fi22E2073.outE] at h
  exact permOfArr_eq_of_rep h

@[expose] noncomputable def S : Set (Equiv.Perm (Fin 3510)) :=
  (fun v => v * fi22OuterZ * v⁻¹) '' (N : Set (Equiv.Perm (Fin 3510)))

theorem base_mem {j : ℕ} (hj : j < 7) :
    PP 3510 12 (AH25R j) ∧ pe (AH25R j) ∈ Subgroup.closure S := by
  have e := baseOK_spec (allN_spec' okBase hj)
  obtain ⟨hv, hve⟩ := ph_eq hPP (tl (AH25T 1) j) L10 L10_lt
  have hz : PP 3510 12 Fi22E2073.E := PP_of_isP (isP_eq ▸ okZ)
  rw [e]
  refine ⟨PP_c hv (PP_c hz hv), Subgroup.subset_closure ⟨phi b (tl (AH25T 1) j), phi_mem _, ?_⟩⟩
  have hinv : (phi b (tl (AH25T 1) j))⁻¹ = phi b (tl (AH25T 1) j) :=
    inv_eq_of_mul_eq_one_right (phi_sq b_comm b_sq _)
  have hve' : pe (phL AH25B (tl (AH25T 1) j) L10) = phi b (tl (AH25T 1) j) := by
    rw [hve, phi_eq]
    rfl
  dsimp only
  rw [pe_c hv (PP_c hz hv), pe_c hz hv, hve', pe_E, hinv, mul_assoc]

theorem reg_mem :
    ∀ k, k < 7 + nR → PP 3510 12 (AH25R k) ∧ pe (AH25R k) ∈ Subgroup.closure S := by
  have hrules := okRules
  rw [Fv8124.strictB_eq] at hrules
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h7 : k < 7
    · exact base_mem h7
    · obtain ⟨r, rfl⟩ : ∃ r, k = 7 + r := ⟨k - 7, by omega⟩
      obtain ⟨ha, hb, e⟩ := ruleOK_spec (allN_spec' hrules (i := r) (by omega))
      obtain ⟨pa, ma⟩ := ih _ ha (by omega)
      obtain ⟨pb, mb⟩ := ih _ hb (by omega)
      rw [e]
      exact ⟨PP_c pa pb, by rw [pe_c pa pb]; exact Subgroup.mul_mem _ ma mb⟩

theorem gen_mem {k : ℕ} (hk : k < 2) :
    fi22GenPerm k ∈ Subgroup.closure S := by
  obtain ⟨h0, h1, e0, e1⟩ := end_spec okEnd
  have h := rep_fi22OrigArrs_nat k (by rw [fi22OrigArrs_size]; exact hk)
  rw [fi22OrigArrs_get hk, Fi22G.gen_eq hk] at h
  rw [← permOfArr_eq_of_rep h]
  change pe (Fi22CGT.F k) ∈ _
  interval_cases k
  · rw [← e0]
    exact (reg_mem _ h0).2
  · rw [← e1]
    exact (reg_mem _ h1).2

theorem facts :
    ∃ N : Subgroup (Equiv.Perm (Fin 3510)), N ≤ fi22P ∧ (∀ v ∈ N, v * v = 1) ∧
      (∀ v ∈ N, ∀ w ∈ N, v * w = w * v) ∧ Nat.card N = 2 ^ 10 ∧
      (∀ v ∈ N, v 0 = 0 → v = 1) ∧
      (∀ q : Fin 3510, (∀ v ∈ N, v q = q → v = 1) → ∃ v ∈ N, v 0 = q) ∧
      fi22P ≤ Subgroup.closure
        ((fun v => v * fi22OuterZ * v⁻¹) '' (N : Set (Equiv.Perm (Fin 3510)))) := by
  refine ⟨N, ?_, fun v hv => ?_, fun v hv w hw => ?_, card_N, fun v hv h => N_reg hv h,
    N_uniq, ?_⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact b_mem hi
  · obtain ⟨m, -, rfl⟩ := exists_phi hv
    exact phi_sq b_comm b_sq m
  · obtain ⟨m, -, rfl⟩ := exists_phi hv
    obtain ⟨m', -, rfl⟩ := exists_phi hw
    rw [← phi_xor b_comm b_sq, ← phi_xor b_comm b_sq, Nat.xor_comm]
  · rw [fi22P_eq]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, rfl⟩
    exact gen_mem k.2

end CertificateChecks.KernelSpor.AH25

end
