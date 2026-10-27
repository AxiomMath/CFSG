
module

public import Certificates.Kernel.U43Mod.Checks3962
public import Certificates.Kernel.U43Mod.LieOddSep
public import CFSG.Certificates.Kernel.U43Mod.Aut3962Sound
public import CFSG.Certificates.Kernel.U43Mod.AutBridge
public import CFSG.Certificates.Kernel.Spor.SiftEq

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Aut3962

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43Aut3962 CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KS.U43Aut3962 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43
  CFSG.Certificates.Native
  CertificateChecks.KernelU43B
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut

theorem cos_abstract {Q : Type*} [Group Q] {δ σ : Q} (h4 : δ ^ 4 = 1)
    (hd : ∀ m, 0 < m → m < 4 → δ ^ m ≠ 1) (hs : ∀ m < 4, δ ^ m * σ ≠ 1) {i j k l : ℕ}
    (hi : i < 4) (hj : j < 2) (hk : k < 4) (hl : l < 2)
    (h : (δ ^ i * σ ^ j)⁻¹ * (δ ^ k * σ ^ l) = 1) : i = k ∧ j = l := by
  have e : δ ^ i * σ ^ j = δ ^ k * σ ^ l := inv_mul_eq_one.1 h
  have A : ∀ a b, a < 4 → b < 4 → δ ^ a = δ ^ b → a = b := by
    have A' : ∀ a b, a < b → b < 4 → δ ^ a ≠ δ ^ b := by
      intro a b hab hb he
      have hsplit : δ ^ b = δ ^ a * δ ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab.le]
      rw [hsplit] at he
      have he' : δ ^ a * δ ^ (b - a) = δ ^ a * 1 := by rw [mul_one]; exact he.symm
      exact hd (b - a) (by omega) (by omega) (mul_left_cancel he')
    intro a b ha hb hab
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact absurd hab (A' a b h1 hb)
    · exact h1
    · exact absurd hab.symm (A' b a h1 ha)
  have B : ∀ a b, a < 4 → b < 4 → δ ^ a ≠ δ ^ b * σ := by
    intro a b ha hb hab
    have hinv : (δ ^ b)⁻¹ = δ ^ (4 - b) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_add, Nat.sub_add_cancel hb.le, h4]
    have hσ : σ = δ ^ (4 - b + a) := by
      rw [pow_add, ← hinv, hab, ← mul_assoc, inv_mul_cancel, one_mul]
    obtain ⟨t, ht⟩ : ∃ t, (8 - (4 - b + a)) % 4 + (4 - b + a) = 4 * t :=
      ⟨((8 - (4 - b + a)) % 4 + (4 - b + a)) / 4, by omega⟩
    apply hs ((8 - (4 - b + a)) % 4) (Nat.mod_lt _ (by norm_num))
    rw [hσ, ← pow_add, ht, pow_mul, h4, one_pow]
  interval_cases j <;> interval_cases l
  · simp only [pow_zero, mul_one] at e
    exact ⟨A i k hi hk e, rfl⟩
  · simp only [pow_zero, pow_one, mul_one] at e
    exact absurd e (B i k hi hk)
  · simp only [pow_zero, pow_one, mul_one] at e
    exact absurd e.symm (B k i hk hi)
  · simp only [pow_one] at e
    exact ⟨A i k hi hk (mul_right_cancel e), rfl⟩

theorem prep_CS {i : ℕ} (hi : i < 2) :
    PRep 820 10 (C.S i) (KernelU43Mod.CP i) ∧ PRep 820 10 (C.SI i) (KernelU43Mod.CP i)⁻¹ :=
  ⟨fun x => (KernelU43Mod.letRep_GA (by omega) x x.2).1,
    fun x => (KernelU43Mod.letRep_GA (by omega) x x.2).2⟩

theorem prep_a : PRep 820 10 (C.S 0) (psi xElt) := by
  rw [← KernelU43Mod.CP_zero]
  exact (prep_CS (by norm_num)).1

theorem prep_b : PRep 820 10 (C.S 1) (psi yElt) := by
  rw [← KernelU43Mod.CP_one]
  exact (prep_CS (by norm_num)).1

theorem prep_ai : PRep 820 10 (C.SI 0) (psi xElt)⁻¹ := by
  rw [← KernelU43Mod.CP_zero]
  exact (prep_CS (by norm_num)).2

theorem prep_bi : PRep 820 10 (C.SI 1) (psi yElt)⁻¹ := by
  rw [← KernelU43Mod.CP_one]
  exact (prep_CS (by norm_num)).2

theorem letV_psi (c : ℕ) : letV (psi xElt) (psi yElt) c = psi (letElt c) := by
  unfold letV letElt
  split_ifs <;> simp

theorem wordElt_foldl (ws : List ℕ) :
    ∀ g : X₀, ws.foldl (fun g l => g * letElt l) g = g * (ws.map letElt).prod := by
  induction ws with
  | nil => intro g; simp
  | cons c ws ih => intro g; rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem psi_wordElt (ws : List ℕ) :
    psi (wordElt ws) = (ws.map fun c => letV (psi xElt) (psi yElt) c).prod := by
  rw [wordElt, wordElt_foldl, one_mul, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun c _ => (letV_psi c).symm

theorem lt_a (c q : ℕ) (hq : q < 820) :
    CFSG.KC.Enum.lt 10 (mask 10) (C.S 0) (C.S 1) (C.SI 0) (C.SI 1) c q =
      (letV (psi xElt) (psi yElt) c ⟨q, hq⟩ : ℕ) :=
  lt_eq_of (fun q hq => prep_a ⟨q, hq⟩) (fun q hq => prep_b ⟨q, hq⟩) (fun q hq => prep_ai ⟨q, hq⟩)
    (fun q hq => prep_bi ⟨q, hq⟩) c q hq

theorem lt_ai (c q : ℕ) (hq : q < 820) :
    CFSG.KC.Enum.lt 10 (mask 10) (C.SI 0) (C.SI 1) (C.S 0) (C.S 1) c q =
      ((letV (psi xElt) (psi yElt) c)⁻¹ ⟨q, hq⟩ : ℕ) := by
  rw [lt_eq_of (x := (psi xElt)⁻¹) (y := (psi yElt)⁻¹) (fun q hq => prep_ai ⟨q, hq⟩)
    (fun q hq => prep_bi ⟨q, hq⟩) (fun q hq => by rw [inv_inv]; exact prep_a ⟨q, hq⟩)
    (fun q hq => by rw [inv_inv]; exact prep_b ⟨q, hq⟩) c q hq]
  congr 2
  unfold letV
  split_ifs <;> simp

theorem wa_eq (ws : List ℕ) (q : ℕ) (hq : q < 820) : wa ws q = (psi (wordElt ws) ⟨q, hq⟩ : ℕ) := by
  rw [psi_wordElt]
  exact mwv_eq lt_a ws q hq

theorem waI_eq (ws : List ℕ) (q : ℕ) (hq : q < 820) :
    waI ws q = ((psi (wordElt ws))⁻¹ ⟨q, hq⟩ : ℕ) := by
  rw [psi_wordElt]
  exact mwvI_eq lt_ai ws q hq

theorem hbase : baseArr = base := base_eq

theorem range_of_prep {X : ℕ} {g : Gp} (hX : PRep 820 10 X g) :
    allN 820 (fun i => Nat.blt (pg 10 (mask 10) X i) 820) = true :=
  CFSG.KS.PackFld.allN_of_forall fun i hi => Nat.blt_eq.mpr (by rw [hX ⟨i, hi⟩]; exact (g _).2)

theorem mem_of_inN {X : ℕ} {g : Gp} (hX : PRep 820 10 X g) (h : inN X = true) : g ∈ Nsub := by
  have hs := siftK_sound binds perm C.hl rfl (range_of_prep hX) h
  rw [← hbase] at hs
  exact (sift_iff (rep_unpack hX)).1 hs

theorem not_mem_of_outN {X : ℕ} {g : Gp} (hX : PRep 820 10 X g) (h : outN X = true) :
    g ∉ Nsub := by
  unfold outN at h
  rw [bAnd_iff] at h
  obtain ⟨hz, hn⟩ := h
  have he := siftK_eq binds perm C.hl rfl (Nat.eq_of_beq_eq_true hz) (range_of_prep hX)
  intro hm
  have hs := (sift_iff (rep_unpack hX)).2 hm
  rw [hbase, he] at hs
  have hs' : inN X = true := hs
  rw [hs'] at hn
  exact Bool.false_ne_true hn

@[expose] noncomputable def DP (j : ℕ) : Gp := permOfArr 820 (unpack 820 10 (DT j))

theorem rep_DP {j : ℕ} (hj : j < 2) :
    Rep 820 (unpack 820 10 (DT j)) (DP j) ∧ Rep 820 (unpack 820 10 (DTI j)) (DP j)⁻¹ :=
  rep_permOfArr (isInvA_unpack (allN_spec kPerm j hj))

theorem kBind_spec : CFSG.KC.BindList.bindListK 10 (mask 10) (DT 0) dTab.toList 0 = true ∧
    CFSG.KC.BindList.bindListK 10 (mask 10) (DT 1) sTab.toList 0 = true :=
  (bAnd_iff _ _).1 kBind

theorem dTab_eq : dTab = unpack 820 10 (DT 0) := unpack_of_bind (by decide) kBind_spec.1

theorem sTab_eq : sTab = unpack 820 10 (DT 1) := unpack_of_bind (by decide) kBind_spec.2

theorem isInvA_cand {t : Array ℕ} {g : Gp} (h : Rep 820 t g) : isInvA 820 t (invCand 820 t) = true :=
  isInvA_of_rep h (rep_invCand h)

theorem dinv : isInvA 820 dTab (invCand 820 dTab) = true := by
  rw [dTab_eq]
  exact isInvA_cand (rep_DP (by norm_num)).1

theorem sinv : isInvA 820 sTab (invCand 820 sTab) = true := by
  rw [sTab_eq]
  exact isInvA_cand (rep_DP (by norm_num)).1

theorem rep_d : Rep 820 dTab dPerm := (rep_permOfArr dinv).1
theorem rep_s : Rep 820 sTab sPerm := (rep_permOfArr sinv).1

theorem dPerm_eq : dPerm = DP 0 := Rep.unique rep_d (dTab_eq ▸ (rep_DP (by norm_num)).1)
theorem sPerm_eq : sPerm = DP 1 := Rep.unique rep_s (sTab_eq ▸ (rep_DP (by norm_num)).1)

theorem prep_d : PRep 820 10 (DT 0) dPerm ∧ PRep 820 10 (DTI 0) dPerm⁻¹ := by
  rw [dPerm_eq]
  exact ⟨prep_of_rep (rep_DP (by norm_num)).1, prep_of_rep (rep_DP (by norm_num)).2⟩

theorem prep_s : PRep 820 10 (DT 1) sPerm ∧ PRep 820 10 (DTI 1) sPerm⁻¹ := by
  rw [sPerm_eq]
  exact ⟨prep_of_rep (rep_DP (by norm_num)).1, prep_of_rep (rep_DP (by norm_num)).2⟩

theorem hn32 : 820 < 2 ^ 32 := by norm_num

theorem conj_gens {j : ℕ} (hj : j < 2) {g : Gp} (hg : PRep 820 10 (DT j) g)
    (hgi : PRep 820 10 (DTI j) g⁻¹) : ∀ n ∈ Nsub, g * n * g⁻¹ ∈ Nsub := by
  have h := allN_spec kConj j hj
  refine conj_mem_N (mem_of_inN (prep_pcomp hn32 (prep_pcomp hn32 hg prep_a) hgi)
    (allN_spec h 0 (by norm_num))) (mem_of_inN (prep_pcomp hn32 (prep_pcomp hn32 hg prep_b) hgi)
    (allN_spec h 1 (by norm_num)))

theorem conj_d : ∀ n ∈ Nsub, dPerm * n * dPerm⁻¹ ∈ Nsub :=
  conj_gens (by norm_num) prep_d.1 prep_d.2

theorem conj_s : ∀ n ∈ Nsub, sPerm * n * sPerm⁻¹ ∈ Nsub :=
  conj_gens (by norm_num) prep_s.1 prep_s.2

theorem mem_Nrm {g : Gp} (hg : ∀ n ∈ Nsub, g * n * g⁻¹ ∈ Nsub) : g ∈ Nrm :=
  mem_Nrm_of_gens (hg _ ⟨xElt, rfl⟩) (hg _ ⟨yElt, rfl⟩)

theorem conj_inv {g : Gp} (hg : ∀ n ∈ Nsub, g * n * g⁻¹ ∈ Nsub) :
    ∀ n ∈ Nsub, g⁻¹ * n * g⁻¹⁻¹ ∈ Nsub := by
  have hi := Nrm.inv_mem (mem_Nrm hg)
  rw [Nrm, Subgroup.mem_set_normalizer_iff] at hi
  exact fun n hn => (hi n).1 hn

theorem conjSift {c : Array ℕ} {g : Gp} (hc : Rep 820 c g) (hg : ∀ n ∈ Nsub, g * n * g⁻¹ ∈ Nsub) :
    ∀ h ∈ [tabA, tabB], siftA 820 (rawLevels 820 chainS baseArr) baseArr 0 (conjTab c h) = true := by
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact (sift_iff (rep_conjTab hc rep_psi_x (rep_invCand hc))).2 (hg _ ⟨xElt, rfl⟩)
  · exact (sift_iff (rep_conjTab hc rep_psi_y (rep_invCand hc))).2 (hg _ ⟨yElt, rfl⟩)

theorem conjN : ∀ g ∈ [dTab, invCand 820 dTab, sTab, invCand 820 sTab], ∀ h ∈ [tabA, tabB],
    siftA 820 (rawLevels 820 chainS baseArr) baseArr 0 (conjTab g h) = true := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact conjSift rep_d conj_d
  · exact conjSift (rep_invCand rep_d) (conj_inv conj_d)
  · exact conjSift rep_s conj_s
  · exact conjSift (rep_invCand rep_s) (conj_inv conj_s)

theorem prep_dPow : ∀ m, PRep 820 10 (dPow m) (dPerm ^ m)
  | 0 => by
    rw [pow_zero]
    exact prep_pidn (by norm_num) (by norm_num)
  | m + 1 => by
    rw [pow_succ']
    exact prep_pcomp hn32 prep_d.1 (prep_dPow m)

theorem d4 : dPerm ^ 4 = 1 := by
  have h1 := prep_pcomp hn32 prep_d.1 (prep_dPow 3)
  have h2 : pc (DT 0) (dPow 3) = pidn 820 10 := Nat.eq_of_beq_eq_true kD4
  have h3 : PRep 820 10 (pidn 820 10) 1 := prep_pidn (by norm_num) (by norm_num)
  refine Equiv.ext fun x => Fin.ext ?_
  have e1 := h1 x
  have e3 := h3 x
  change pg 10 (mask 10) (pc (DT 0) (dPow 3)) x = _ at e1
  rw [h2, e3, ← pow_succ'] at e1
  exact e1.symm

theorem out_spec {m : ℕ} (hm : m < 4) :
    bIf(Nat.beq m 0, true, outN (dPow m)) = true ∧ outN (pc (dPow m) (DT 1)) = true :=
  (bAnd_iff _ _).1 (allN_spec kOut m hm)

theorem dpow_not_mem : ∀ m, 0 < m → m < 4 → dPerm ^ m ∉ Nsub := by
  intro m h0 h4
  have h := (out_spec h4).1
  interval_cases m
  · exact not_mem_of_outN (prep_dPow 1) h
  · exact not_mem_of_outN (prep_dPow 2) h
  · exact not_mem_of_outN (prep_dPow 3) h

theorem dpow_s_not_mem (m : ℕ) (hm : m < 4) : dPerm ^ m * sPerm ∉ Nsub :=
  not_mem_of_outN (prep_pcomp hn32 (prep_dPow m) prep_s.1) (out_spec hm).2

theorem rep_ds (i j : ℕ) : Rep 820 (dsElt i j) (dsPerm i j) :=
  rep_compA (rep_powTab_perm rep_d i) (rep_powTab_perm rep_s j)

theorem cos_eq {i j k l : ℕ} (hi : i < 4) (hj : j < 2) (hk : k < 4) (hl : l < 2)
    (h : (dsPerm i j)⁻¹ * dsPerm k l ∈ Nsub) : i = k ∧ j = l := by
  let D : Nrm := ⟨dPerm, mem_Nrm conj_d⟩
  let S : Nrm := ⟨sPerm, mem_Nrm conj_s⟩
  have key : ∀ x : Nrm, ((x : Nrm ⧸ Nsub.subgroupOf Nrm) = 1 ↔ (x : Gp) ∈ Nsub) := fun x => by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine cos_abstract (δ := ((D : Nrm) : Nrm ⧸ Nsub.subgroupOf Nrm)) (σ := (S : Nrm ⧸ _)) ?_ ?_ ?_
    hi hj hk hl ?_
  · rw [← QuotientGroup.mk_pow, key]
    simp [D, d4]
  · intro m h0 h4
    rw [← QuotientGroup.mk_pow, Ne, key]
    simpa [D] using dpow_not_mem m h0 h4
  · intro m hm
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, Ne, key]
    simpa [D, S] using dpow_s_not_mem m hm
  · rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
      ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, key]
    simpa [D, S, dsPerm] using h

theorem cos : ∀ i < 4, ∀ j < 2, isInvA 820 (dsElt i j) (invCand 820 (dsElt i j)) = true ∧
    ∀ k < 4, ∀ l < 2, (i = k ∧ j = l) ∨
      siftA 820 (rawLevels 820 chainS baseArr) baseArr 0
        (compA 820 (invCand 820 (dsElt i j)) (dsElt k l)) = false := by
  intro i hi j hj
  have hinv := isInvA_cand (rep_ds i j)
  refine ⟨hinv, fun k hk l hl => ?_⟩
  by_cases hh : i = k ∧ j = l
  · exact Or.inl hh
  · refine Or.inr ?_
    have hrep := rep_compA (rep_inv_of_isInvA (rep_ds i j) hinv) (rep_ds k l)
    cases e : siftA 820 (rawLevels 820 chainS baseArr) baseArr 0
        (compA 820 (invCand 820 (dsElt i j)) (dsElt k l))
    · rfl
    · exact absurd (cos_eq hi hj hk hl ((sift_iff hrep).1 e)) hh

theorem cenOK_of {b : ℕ} (hb : b < 820) {g0 g1 : List ℕ × List ℕ} {z0 z1 : Gp}
    (h0 : (psi (wordElt g0.2))⁻¹ * psi (wordElt g0.1) = z0)
    (h1 : (psi (wordElt g1.2))⁻¹ * psi (wordElt g1.1) = z1)
    (f0 : z0 ⟨b, hb⟩ = ⟨b, hb⟩) (f1 : z1 ⟨b, hb⟩ = ⟨b, hb⟩)
    (honly : ∀ q : Fin 820, z0 q = q → z1 q = q → (q : ℕ) = b) :
    cenOK (b, [g0, g1]) = true := by
  have hinv : ∀ gt : List ℕ × List ℕ, isInvA 820 (wordTab gt.2) (invCand 820 (wordTab gt.2)) = true :=
    fun gt => isInvA_cand (rep_wordTab gt.2)
  have hrep : ∀ gt : List ℕ × List ℕ,
      Rep 820 (stabElt gt) ((psi (wordElt gt.2))⁻¹ * psi (wordElt gt.1)) := fun gt =>
    rep_compA (rep_inv_of_isInvA (rep_wordTab gt.2) (hinv gt)) (rep_wordTab gt.1)
  have r0 : Rep 820 (stabElt g0) z0 := h0 ▸ hrep g0
  have r1 : Rep 820 (stabElt g1) z1 := h1 ▸ hrep g1
  unfold cenOK
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hinv g0, ?_⟩, hinv g1, ?_⟩, fun q hq => ?_⟩
  · rw [r0.apply hb, f0]
  · rw [r1.apply hb, f1]
  · rw [r0.apply hq, r1.apply hq]
    by_cases hz : (z0 ⟨q, hq⟩ : ℕ) = q ∧ (z1 ⟨q, hq⟩ : ℕ) = q
    · have hqb : q = b := honly ⟨q, hq⟩ (Fin.ext hz.1) (Fin.ext hz.2)
      subst hqb
      simp
    · have hf : ((z0 ⟨q, hq⟩ : ℕ) == q && (z1 ⟨q, hq⟩ : ℕ) == q) = false := by
        rcases not_and_or.1 hz with h | h <;> simp [h]
      rw [hf]
      rfl

@[expose] noncomputable def ZP (k : ℕ) : Gp := permOfArr 820 (unpack 820 10 (ZT k))

theorem cen_spec {i j : ℕ} (hi : i < 2) (hj : j < 2) :
    permOK 820 10 (mask 10) (820 * 10) (ZT (2 * i + j)) (ZTI (2 * i + j)) = true ∧
      inN (ZT (2 * i + j)) = true ∧
      baseEq bs (pg 10 (mask 10) (ZT (2 * i + j))) (stabPt (cg i j)) = true ∧
      Nat.beq (pg 10 (mask 10) (ZT (2 * i + j)) (bp i)) (bp i) = true := by
  have h := allN_spec kCen (2 * i + j) (by omega)
  beta_reduce at h
  rw [CFSG.KS.U43Mod.strictB_eq, CFSG.KS.U43Mod.strictB_eq, CFSG.KS.U43Mod.strictB_eq] at h
  have e1 : Nat.shiftRight (2 * i + j) 1 = i := by
    interval_cases i <;> interval_cases j <;> rfl
  have e2 : Nat.land (2 * i + j) 1 = j := by
    interval_cases i <;> interval_cases j <;> rfl
  rw [e1, e2, bAnd_iff, bAnd_iff, bAnd_iff] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem bp_lt {i : ℕ} (hi : i < 2) : bp i < 820 := by
  interval_cases i <;> decide +kernel

theorem ZP_eq {i j : ℕ} (hi : i < 2) (hj : j < 2) :
    (psi (wordElt (cg i j).2))⁻¹ * psi (wordElt (cg i j).1) = ZP (2 * i + j) ∧
      ZP (2 * i + j) ⟨bp i, bp_lt hi⟩ = ⟨bp i, bp_lt hi⟩ := by
  obtain ⟨hp, hin, hbs, hfix⟩ := cen_spec hi hj
  have hr : PRep 820 10 (ZT (2 * i + j)) (ZP (2 * i + j)) :=
    prep_of_rep (rep_permOfArr (isInvA_unpack hp)).1
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 (mem_of_inN hr hin)
  have hbs' := CFSG.KS.U43Mod.baseEq_iff.1 hbs
  have hag : ∀ p (hp : p < 820), p ∈ bs →
      psi ((wordElt (cg i j).2)⁻¹ * wordElt (cg i j).1) ⟨p, hp⟩ = psi u ⟨p, hp⟩ := by
    intro p hp hpb
    apply Fin.ext
    have e : (psi u ⟨p, hp⟩ : ℕ) = stabPt (cg i j) p := by
      rw [hu]
      exact (hr ⟨p, hp⟩).symm.trans (hbs' p hpb)
    rw [e, map_mul, map_inv, Equiv.Perm.mul_apply]
    unfold stabPt
    rw [wa_eq _ p hp, waI_eq _ _ (Fin.is_lt _)]
  have hsep := KernelU43Mod.psi_sep _ u (hag 0 (by norm_num) (by decide))
    (hag 1 (by norm_num) (by decide)) (hag 9 (by norm_num) (by decide))
  refine ⟨?_, ?_⟩
  · rw [← map_inv, ← map_mul, hsep, hu]
  · apply Fin.ext
    rw [← hr ⟨bp i, bp_lt hi⟩]
    exact Nat.eq_of_beq_eq_true hfix

theorem fix_only {i : ℕ} (hi : i < 2) (q : Fin 820) (h0 : ZP (2 * i) q = q)
    (h1 : ZP (2 * i + 1) q = q) : (q : ℕ) = bp i := by
  have h := allN_spec kFix i hi
  beta_reduce at h
  rw [CFSG.KS.U43Mod.strictB_eq, CFSG.KS.U43Mod.strictB_eq, CFSG.KS.U43Mod.strictB_eq] at h
  have hq := allN_spec h q q.2
  beta_reduce at hq
  have r0 : PRep 820 10 (ZT (2 * i)) (ZP (2 * i)) :=
    prep_of_rep (rep_permOfArr (isInvA_unpack (cen_spec hi (j := 0) (by norm_num)).1)).1
  have r1 : PRep 820 10 (ZT (2 * i + 1)) (ZP (2 * i + 1)) :=
    prep_of_rep (rep_permOfArr (isInvA_unpack (cen_spec hi (j := 1) (by norm_num)).1)).1
  have e0 : Nat.beq (pg 10 (mask 10) (ZT (2 * i)) q) q = true := by
    have := r0 q
    rw [h0] at this
    rw [this]
    exact Nat.beq_refl _
  have e1 : Nat.beq (pg 10 (mask 10) (ZT (2 * i + 1)) q) q = true := by
    have := r1 q
    rw [h1] at this
    rw [this]
    exact Nat.beq_refl _
  simp only [Nat.mul_eq, Nat.succ_eq_add_one] at hq
  rw [e0, e1] at hq
  exact Nat.eq_of_beq_eq_true hq

theorem cenGens_eq : cenGens = [(bp 0, [cg 0 0, cg 0 1]), (bp 1, [cg 1 0, cg 1 1])] := by
  decide +kernel

theorem cen : ∀ x ∈ cenGens, cenOK x = true := by
  have hcase : ∀ i < 2, cenOK (bp i, [cg i 0, cg i 1]) = true := by
    intro i hi
    obtain ⟨e0, f0⟩ := ZP_eq hi (j := 0) (by norm_num)
    obtain ⟨e1, f1⟩ := ZP_eq hi (j := 1) (by norm_num)
    rw [Nat.add_zero] at e0 f0
    exact cenOK_of (bp_lt hi) e0 e1 f0 f1 (fun q h0 h1 => fix_only hi q h0 h1)
  rw [cenGens_eq]
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact hcase 0 (by norm_num)
  · exact hcase 1 (by norm_num)

theorem bases : cenGens.map (·.1) = [0, 4] := by decide +kernel

theorem trans_length : U43Aut.trans.length = 820 := by decide +kernel

theorem tBase_eq (e : ℕ × List ℕ) : tBase e = if e.1 = 0 then 0 else 4 := by
  unfold tBase
  by_cases h : e.1 = 0
  · rw [if_pos h, h]
    rfl
  · have hb : Nat.beq e.1 0 = false := by
      cases hb : Nat.beq e.1 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [if_neg h, hb]

theorem transOK_all : ∀ r < 820, transOK r = true := by
  intro r hr
  have hr' : r < U43Aut.trans.length := by rw [trans_length]; exact hr
  have h := allIdx_spec _ 0 kTrans r hr'
  rw [Nat.zero_add] at h
  have hget : U43Aut.trans[r]! = U43Aut.trans[r] := getElem!_pos U43Aut.trans r hr'
  set e := U43Aut.trans[r] with he
  have key : ∀ b (hb : b < 820), tBase e = b → (wordTab e.2)[b]! = r := by
    intro b hb htb
    rw [(rep_wordTab e.2).apply hb, ← wa_eq e.2 b hb, ← htb]
    exact Nat.eq_of_beq_eq_true h
  unfold transOK
  simp only
  rw [hget]
  have htb := tBase_eq e
  split_ifs with h0
  · rw [beq_iff_eq] at h0
    rw [if_pos h0] at htb
    rw [key 0 (by norm_num) htb]
    exact beq_self_eq_true r
  · rw [beq_iff_eq] at h0
    rw [if_neg h0] at htb
    rw [key 4 (by norm_num) htb]
    exact beq_self_eq_true r

theorem autFacts3962 : AutFacts := ⟨dinv, sinv, conjN, cos, cen, bases, transOK_all⟩

theorem u43AutCheck_true : u43AutCheck () = true :=
  CFSG.KS.U43Mod.LieOdd.u43AutCheck_of autFacts3962

end CertificateChecks.KernelU43Aut3962

end
