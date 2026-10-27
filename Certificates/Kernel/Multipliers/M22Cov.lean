module

public import Certificates.Kernel.Multipliers.TwoCover
public import Certificates.Kernel.Multipliers.U43Cone
public import Certificates.Kernel.Multipliers.ZProd
public import Certificates.Kernel.Multipliers.Ent
public import Certificates.Certificate24093
public import CFSG.Certificates.Kernel.Bounds.M22CovAlt.Checks.C
public import CFSG.Certificates.Kernel.Bounds.M22CovAlt.Checks.M

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelM22Cov

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE CFSG.Certificates.LabZ CFSG.LieType.Multipliers
  CFSG.CosetTable CertificateChecks.KernelMult CertificateChecks.KernelTwoCover
  CFSG.Certificates.CosetEnumeration CFSG.Sporadic.Recognition.M22Multiplier

variable {m : ℕ}

theorem zprod_eq_two {G : Type*} [Group G] {g : ℕ → G} {D k l : ℕ} (hkl : k < l) (hl : l < D)
    {t : ℕ → ℤ} (h : ∀ d < D, d ≠ k → d ≠ l → g d ^ t d = 1) :
    zprod g D t = g k ^ t k * g l ^ t l := by
  induction D with
  | zero => omega
  | succ D ih =>
    rw [zprod_succ]
    rcases Nat.lt_or_ge l D with hlD | hlD
    · rw [ih hlD fun d hd h1 h2 => h d (by omega) h1 h2, h D (by omega) (by omega) (by omega),
        mul_one]
    · have e : l = D := by omega
      subst e
      rw [zprod_eq_pow hkl fun d hd hdk => h d (by omega) hdk (by omega)]

theorem card_le_mul (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool))
    [Finite (PG m R)] {n : ℕ} (hn : 0 < n) {z : PG m (coverWords R w)}
    (hz : z ∈ Subgroup.center _) (hzn : z ^ n = 1)
    (hR : ∀ k < R.length, zk R w k ∈ Subgroup.zpowers z) :
    Finite (PG m (coverWords R w)) ∧ Nat.card (PG m (coverWords R w)) ≤ Nat.card (PG m R) * n := by
  have : (Subgroup.zpowers z).Normal :=
    Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr hz)
  have hfo : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hzn⟩
  have : Finite (Subgroup.zpowers z) := finite_zpowers.mpr hfo
  obtain ⟨f, c⟩ := card_le_mul_of_relators R (coverWords R w) (Subgroup.zpowers z) (fun r hr => by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
      have := hR k hk
      simpa only [zk, List.getD_eq_getElem _ _ hk] using this)
  have h2 : Nat.card (Subgroup.zpowers z) ≤ n := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hn hzn
  exact ⟨f, c.trans (Nat.mul_le_mul_left _ h2)⟩

theorem dvd_orderOf_of_mono {N n : ℕ} (R : List (List (Fin m × Bool)))
    (w : Fin m → List (Fin m × Bool)) {Rc Wc : List (List ℕ)} (hR : codes R = Rc)
    (hW : codes ((List.finRange m).map fun i => (i, false) :: w i) = Wc) {T C : ℕ → ℕ}
    (hp : CFSG.KC.Mono.paramsOK N n C R.length = true)
    (h : ∀ x < N, CFSG.KC.Mono.pointOK T m N n C Rc Wc x = true) {k : ℕ} (hk : k < R.length)
    (hC : C k = 1) : n ∣ orderOf (zk R w k) := by
  obtain ⟨E, _, ψ, τ, hτ, hψ⟩ := CFSG.Certificates.Mono.mono_sound R w hR hW hp h
  have e : ψ (zk R w k) = τ (Multiplicative.ofAdd (1 : ZMod n)) := by
    rw [zk, List.getD_eq_getElem _ _ hk, hψ k hk, hC, Nat.cast_one]
  have h1 : orderOf (ψ (zk R w k)) = n := by
    rw [e, orderOf_injective τ hτ, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  rw [← h1]
  exact orderOf_map_dvd ψ _

abbrev cov : List (List (Fin 2 × Bool)) := coverWords m22Rels m22CommWord

noncomputable abbrev z (k : ℕ) : PG 2 cov := zk m22Rels m22CommWord k

noncomputable abbrev gen : ℕ → PG 2 cov := CFSG.KC.MiscCoset.pgGen cov

noncomputable def gg (d : ℕ) : PG 2 cov :=
  if d < 8 then bval gen (wWord (CFSG.KD.M22C.selRT d)) (wLen (CFSG.KD.M22C.selRT d))
  else if d = 8 then bval gen (wWord (CFSG.KD.M22C.selST 0)) (wLen (CFSG.KD.M22C.selST 0)) else 1

theorem rel_ent : ∀ k < 6, CFSG.KD.M22C.selRT k = ent (m22Rels.getD k []) := by
  decide +kernel

theorem cover_ent0 : CFSG.KD.M22C.selRT 6 = ent ((0, false) :: m22CommWord 0) := by
  decide +kernel

theorem cover_ent1 : CFSG.KD.M22C.selRT 7 = ent ((1, false) :: m22CommWord 1) := by
  decide +kernel

theorem gg_rel {k : ℕ} (hk : k < 6) : gg k = z k := by
  have hl : ∀ k < 6, (m22Rels.getD k []).length < 1024 := by decide +kernel
  simp only [gg, show k < 8 by omega, ↓reduceIte]
  rw [bval_ent (by norm_num) cov _ (rel_ent k hk) (hl k hk)]
  rfl

theorem gg_cover {i : ℕ} (hi : i < 2) : gg (6 + i) = 1 := by
  have h8 : 6 + i < 8 := by omega
  simp only [gg, h8, ↓reduceIte]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [bval_ent (by norm_num) cov _ cover_ent0 (by decide +kernel)]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (cover_mem m22Rels m22CommWord 0))
  · rw [bval_ent (by norm_num) cov _ cover_ent1 (by decide +kernel)]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (cover_mem m22Rels m22CommWord 1))

theorem gg_central {r : ℕ} (hr : r < 8) : gg r ∈ Subgroup.center (PG 2 cov) := by
  rcases Nat.lt_or_ge r 6 with h | h
  · exact gg_rel h ▸ zk_central m22Rels m22CommWord (by simpa [m22Rels] using h)
  · have e : r = 6 + (r - 6) := by omega
    rw [e, gg_cover (by omega)]
    exact Subgroup.one_mem _

theorem gg_center_or (d : ℕ) : gg d ∈ Subgroup.center (PG 2 cov) ∨ gg d = gg 8 := by
  rcases Nat.lt_or_ge d 8 with h | h
  · exact Or.inl (gg_central h)
  · rcases Nat.lt_or_ge d 9 with h' | h'
    · exact Or.inr (by rw [show d = 8 by omega])
    · left
      simp only [gg, show ¬ (d < 8) from by omega, show ¬ (d = 8) from by omega, ↓reduceIte]
      exact Subgroup.one_mem _

theorem gg_comm (i j : ℕ) : Commute (gg i) (gg j) := by
  rcases gg_center_or i with hi | hi
  · exact (Subgroup.mem_center_iff.mp hi (gg j)).symm
  rcases gg_center_or j with hj | hj
  · exact Subgroup.mem_center_iff.mp hj (gg i)
  rw [hi, hj]

theorem hRT : ∀ r < 8, wWord (CFSG.KD.M22C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.M22C.selRT r)) ∧
    bval gen (wWord (CFSG.KD.M22C.selRT r)) (wLen (CFSG.KD.M22C.selRT r)) = gg r ∧
      ∀ c, Commute (letV gen c) (gg r) := by
  have hcl : ∀ r < 8, wWord (CFSG.KD.M22C.selRT r) < 2 ^ (8 * wLen (CFSG.KD.M22C.selRT r)) := by
    decide +kernel
  intro r hr
  refine ⟨hcl r hr, ?_, fun c => Subgroup.mem_center_iff.mp (gg_central hr) _⟩
  simp only [gg, hr, ↓reduceIte]

theorem hST : ∀ j < 1, bval gen (wWord (CFSG.KD.M22C.selST j)) (wLen (CFSG.KD.M22C.selST j)) =
    gg (8 + j) := by
  intro j hj
  have : j = 0 := by omega
  subst this
  simp only [gg, show ¬ (8 + 0 < 8) from by omega, show 8 + 0 = 8 from rfl, ↓reduceIte]

theorem cyc_of {c wid R V : ℕ} (hc : c < 2 ^ 20) (hwid : wid < 512)
    (h : LabZ.cycZ CFSG.KD.M22C.blk CFSG.KD.M22C.selWT CFSG.KD.M22C.LB CFSG.KD.M22C.BIAS 2129 c wid R V
      = true) :
    zprod gg 9 (decZ V) = zprod gg 9 (decZ (CFSG.KD.M22C.TG wid)) :=
  cyc_sound gen gg gg_comm
    (KernelU43.coneOk_intro CFSG.KD.M22C.sH0 CFSG.KD.M22C.sH1 (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) CFSG.KD.M22C.sH6 CFSG.KD.M22C.sI CFSG.KD.M22C.sH7 CFSG.KD.M22C.sH8
      CFSG.KD.M22C.sW CFSG.KD.M22C.sL)
    hRT hST rfl hc hwid h

theorem rel_of {c wid R V : ℕ} (ρ : List ℤ) (hc : c < 2 ^ 20) (hwid : wid < 512)
    (h : LabZ.cycZ CFSG.KD.M22C.blk CFSG.KD.M22C.selWT CFSG.KD.M22C.LB CFSG.KD.M22C.BIAS 2129 c wid R V
      = true)
    (hρ : ∀ d < 9, decZ V d - decZ (CFSG.KD.M22C.TG wid) d = ρ.getD d 0) :
    zprod gg 9 (fun d => ρ.getD d 0) = 1 := by
  rw [← zprod_congr gg hρ]
  change zprod gg 9 (decZ V - decZ (CFSG.KD.M22C.TG wid)) = 1
  rw [zprod_sub gg_comm, cyc_of hc hwid h, mul_inv_cancel]

@[expose] def rhos : List (List ℤ) :=
  [[0, 0, -1, 0, 0, 0, 0, 0, 11], [-1, 0, 0, 1, -1, 0, 0, 0, 0], [2, -3, 0, -1, 1, 0, -1, 0, 0],
    [0, 2, 0, -1, 1, 0, 0, -1, 0], [-16, 7, -1, -1, 1, 4, -7, -4, 11],
    [-1, -16, 4, 0, 4, 1, -1, 12, -11], [6, -7, 3, 0, 5, -3, 5, -1, 0]]

theorem rhos_one : ∀ ρ ∈ rhos, zprod gg 9 (fun d => ρ.getD d 0) = 1 := by
  have h := CFSG.KD.M22C.cyc_all
  intro ρ hρ
  simp only [rhos, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 0 (by decide)) (by decide +kernel)
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 1 (by decide)) (by decide +kernel)
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 2 (by decide)) (by decide +kernel)
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 3 (by decide)) (by decide +kernel)
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 4 (by decide)) (by decide +kernel)
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 5 (by decide)) (by decide +kernel)
  · exact rel_of _ (by decide +kernel) (by decide +kernel) (h 6 (by decide)) (by decide +kernel)

theorem pow_off {t : List ℤ} {k l : ℕ}
    (ht : ∀ d < 9, d ≠ k → d ≠ l → d ≠ 6 → d ≠ 7 → t.getD d 0 = 0) :
    ∀ d < 9, d ≠ k → d ≠ l → gg d ^ t.getD d 0 = 1 := by
  intro d hd hk hl
  by_cases h6 : d = 6
  · subst h6
    rw [gg_cover (i := 0) (by omega), one_zpow]
  by_cases h7 : d = 7
  · subst h7
    rw [gg_cover (i := 1) (by omega), one_zpow]
  rw [ht d hd hk hl h6 h7, zpow_zero]

theorem z_eq_one {k : ℕ} (hk : k < 6) (cs t : List ℤ)
    (ht : ∀ d < 9, (List.zipWith (fun c ρ => c • ρ) cs (rhos.map fun ρ d => ρ.getD d 0)).sum d =
      t.getD d 0) (h1 : t.getD k 0 = 1)
    (hoff : ∀ d < 9, d ≠ k → d ≠ k → d ≠ 6 → d ≠ 7 → t.getD d 0 = 0) : z k = 1 := by
  have e := zprod_target gg_comm 9 cs rhos rhos_one t ht
  rw [zprod_eq_single (k := k) (by omega) h1 fun d hd hdk => pow_off hoff d hd hdk hdk] at e
  rw [← gg_rel hk, e]

theorem z0_eq : z 0 = 1 :=
  z_eq_one (by omega) [0, -5, -2, -3, 0, 0, 0] [1, 0, 0, 0, 0, 0, 2, 3, 0] (by decide +kernel) rfl
    (by decide)

theorem z1_eq : z 1 = 1 :=
  z_eq_one (by omega) [0, -2, -1, -1, 0, 0, 0] [0, 1, 0, 0, 0, 0, 1, 1, 0] (by decide +kernel) rfl
    (by decide)

theorem z3_eq : z 3 = 1 :=
  z_eq_one (by omega) [-2, -21, -6, -17, 1, -1, 1] [0, 0, 0, 1, 0, 0, 5, 0, 0] (by decide +kernel)
    rfl (by decide)

theorem z4_eq : z 4 = 1 :=
  z_eq_one (by omega) [-2, -17, -4, -14, 1, -1, 1] [0, 0, 0, 0, 1, 0, 3, -3, 0] (by decide +kernel)
    rfl (by decide)

theorem z5_mul : z 2 ^ (3 : ℤ) * z 5 = 1 := by
  have t := zprod_target gg_comm 9 [9, 31, -2, 37, -4, 5, -4] rhos rhos_one
    [0, 0, 3, 0, 0, 1, 5, 43, 0] (by decide +kernel)
  rw [zprod_eq_two (k := 2) (l := 5) (by omega) (by omega) (pow_off (by decide))] at t
  rw [← gg_rel (k := 2) (by omega), ← gg_rel (k := 5) (by omega)]
  simpa using t

theorem z2_pow : z 2 ^ 12 = 1 := by
  have t := zprod_target gg_comm 9 [37, 194, 19, 192, -17, 20, -16] rhos rhos_one
    [0, 0, 12, 0, 0, 0, 0, 132, 0] (by decide +kernel)
  rw [zprod_eq_pow (k := 2) (by omega) fun d hd hdk => pow_off (k := 2) (l := 2) (by decide) d hd hdk hdk]
    at t
  rw [← gg_rel (by omega)]
  exact_mod_cast t

theorem card_le : Finite (PG 2 cov) ∧ Nat.card (PG 2 cov) ≤ 5322240 := by
  obtain ⟨hfin, hcard⟩ := Certificates.certificate24093.2
  obtain ⟨f, c⟩ := card_le_mul m22Rels m22CommWord (n := 12) (by norm_num)
    (zk_central m22Rels m22CommWord (k := 2) (by decide)) z2_pow (fun k hk => by
      have hk' : k < 6 := by simpa [m22Rels] using hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show zk m22Rels m22CommWord 0 = z 0 from rfl, z0_eq]
        exact Subgroup.one_mem _
      · rw [show zk m22Rels m22CommWord 1 = z 1 from rfl, z1_eq]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
      · rw [show zk m22Rels m22CommWord 3 = z 3 from rfl, z3_eq]
        exact Subgroup.one_mem _
      · rw [show zk m22Rels m22CommWord 4 = z 4 from rfl, z4_eq]
        exact Subgroup.one_mem _
      · rw [show zk m22Rels m22CommWord 5 = z 5 from rfl, eq_inv_of_mul_eq_one_right z5_mul]
        exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers _ _))
  exact ⟨f, c.trans (by omega)⟩

theorem codes_rels : codes m22Rels = CFSG.KD.M22M.Rc := by
  decide +kernel

theorem codes_cover :
    codes ((List.finRange 2).map fun i => (i, false) :: m22CommWord i) = CFSG.KD.M22M.Wc := by
  decide +kernel

theorem twelve_dvd : 12 ∣ orderOf (z 2) :=
  dvd_orderOf_of_mono m22Rels m22CommWord codes_rels codes_cover CFSG.KD.M22M.sQ
    CFSG.KD.M22M.pt_all (k := 2) (by decide) rfl

theorem bounds : Finite (PG 2 m22Cover) ∧ Nat.card (PG 2 m22Cover) ≤ 5322240 ∧
    12 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ m22Cover.map FreeGroup.mk}
      (FreeGroup.mk m22B11)) :=
  ⟨card_le.1, card_le.2, twelve_dvd⟩

end CertificateChecks.KernelM22Cov

end
