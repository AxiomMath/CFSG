module

public import Certificates.Kernel.G24Cls.Chk27204
public import Certificates.Kernel.G24Cls.C27203
public import CFSG.Certificates.Kernel.G24OutSound

public section

set_option maxRecDepth 400000
set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelG24.Out27204

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.G24Key CFSG.KC.G24Tri
  CertificateChecks.KernelG24.Tri27206 CertificateChecks.KernelG24.Cls27203
  CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Co1Block CFSG.EvenSporadicStandard.Induction.AutBound

section Ext

variable {G : Type*} [Group G]

@[expose] def extT (T : Subgroup G) (τ : G) (hn : ∀ x ∈ T, τ * x * τ⁻¹ ∈ T) (h2 : τ * τ ∈ T) :
    Subgroup G where
  carrier := {g | g ∈ T ∨ g * τ⁻¹ ∈ T}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (mul_mem ha hb)
    · refine Or.inr ?_
      rw [mul_assoc]
      exact mul_mem ha hb
    · refine Or.inr ?_
      have e : a * b * τ⁻¹ = a * τ⁻¹ * (τ * b * τ⁻¹) := by group
      rw [e]
      exact mul_mem ha (hn b hb)
    · refine Or.inl ?_
      have e : a * b = a * τ⁻¹ * (τ * (b * τ⁻¹) * τ⁻¹) * (τ * τ) := by group
      rw [e]
      exact mul_mem (mul_mem ha (hn _ hb)) h2
  one_mem' := Or.inl (one_mem T)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (inv_mem ha)
    · refine Or.inr ?_
      have e : a⁻¹ * τ⁻¹ = (τ * (a * τ⁻¹) * τ⁻¹ * (τ * τ))⁻¹ := by group
      rw [e]
      exact inv_mem (mul_mem (hn _ ha) h2)

theorem mem_extT {T : Subgroup G} {τ : G} {hn : ∀ x ∈ T, τ * x * τ⁻¹ ∈ T} {h2 : τ * τ ∈ T}
    {g : G} : g ∈ extT T τ hn h2 ↔ g ∈ T ∨ g * τ⁻¹ ∈ T := Iff.rfl

theorem card_extT {T : Subgroup G} [Finite T] {τ : G} (hn : ∀ x ∈ T, τ * x * τ⁻¹ ∈ T)
    (h2 : τ * τ ∈ T) (hτ : τ ∉ T) : Nat.card (extT T τ hn h2) = 2 * Nat.card T := by
  have hset : ((extT T τ hn h2 : Subgroup G) : Set G) = (T : Set G) ∪ (· * τ) '' (T : Set G) := by
    ext g
    change g ∈ T ∨ g * τ⁻¹ ∈ T ↔ _
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨g * τ⁻¹, h, by simp⟩
    · rintro (h | ⟨t, ht, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (by simpa using ht)
  have hfin : (T : Set G).Finite := Set.toFinite _
  have hdisj : Disjoint (T : Set G) ((· * τ) '' (T : Set G)) := by
    rw [Set.disjoint_left]
    rintro g hg ⟨t, ht, rfl⟩
    apply hτ
    have : t⁻¹ * (t * τ) ∈ T := mul_mem (inv_mem ht) hg
    simpa using this
  have hc1 : Nat.card (extT T τ hn h2) = ((extT T τ hn h2 : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  have hc2 : Nat.card T = (T : Set G).ncard := Nat.card_coe_set_eq _
  rw [hc1, hc2, hset, Set.ncard_union_eq hdisj hfin (hfin.image _),
    Set.ncard_image_of_injective _ (mul_left_injective τ)]
  ring

theorem mem_normalizer_of_conj {H : Subgroup G} [Finite H] {a b g : G}
    (hH : H = Subgroup.closure {a, b}) (ha : g * a * g⁻¹ ∈ H) (hb : g * b * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  let φ : G →* G := (MulAut.conj g).toMonoidHom
  have hle : H.map φ ≤ H := by
    rw [Subgroup.map_le_iff_le_comap]
    conv_lhs => rw [hH]
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hb
  have hcard : Nat.card (H.map φ) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : H.map φ = H := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hle ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨h', hh', hh'e⟩ := hh
    have : h' = h := (MulAut.conj g).injective hh'e
    rwa [← this]

end Ext

theorem band_l {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> simp_all

theorem band_r {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> simp_all

theorem ptRep_unique {P : ℕ} {g h : Pm} (hg : PtRep P g) (hh : PtRep P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem rep_of_ptRep {P : ℕ} {g : Pm} (hP : PtRep P g) : Rep 1365 (unpack 1365 11 P) g :=
  fun x => by rw [← ap_eq_unpack P x.2]; exact hP x

theorem ptRep_pcomp {p q : ℕ} {g h : Pm} (hp : PtRep p g) (hq : PtRep q h) :
    PtRep (pcomp 1365 11 (mask 11) p q) (g * h) := fun x => by
  rw [ap_eq_pg, CFSG.KS.PackFld.pg_pcomp (by norm_num) x.2, ← ap_eq_pg, ← ap_eq_pg, hq, hp]
  rfl

theorem o_inv {o : Pm} (hO : PtRep (PK 7) o) (hOi : PtRep (PK 7) o⁻¹) : o⁻¹ = o :=
  ptRep_unique hOi hO

theorem o_sq {o : Pm} (hO : PtRep (PK 7) o) (hOi : PtRep (PK 7) o⁻¹) : o * o = 1 := by
  nth_rewrite 2 [← o_inv hO hOi]
  exact mul_inv_cancel o

theorem canO : canonK 1365 11 (mask 11) (1365 * 11) (PK 7) = true :=
  CFSG.KC.Pack.allN_spec Tri27206.kCan 7 (by norm_num)

theorem rep_oa : Rep 1365 oa (permOfArr 1365 (unpack 1365 11 (PK 7))) := by
  have e : oa = unpack 1365 11 (sP 2) := oa_eq
  rw [e]
  exact (rep_of_invEqK (band_l kInvO)).1

theorem sign_o {o : Pm} (hO : PtRep (PK 7) o) : Equiv.Perm.sign o = -1 := by
  rw [CFSG.KC.Pack.sign_of_signK kSignO fun i => by rw [← ap_eq_pg]; exact (hO i).symm]
  exact Odd.neg_one_pow ⟨325, rfl⟩

section Main


theorem mem_of_pcomp {p q : ℕ} {g h : Pm} (hp : PtRep p g) (hq : PtRep q h)
    (cp : canonK 1365 11 (mask 11) (1365 * 11) p = true)
    (cq : canonK 1365 11 (mask 11) (1365 * 11) q = true)
    (hs : siftK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) LC.LR LC.TRI LC.BP 3 0
      (pcomp 1365 11 (mask 11) p q) = true) : g * h ∈ twoBD :=
  mem_of_sift (rep_of_ptRep (ptRep_pcomp hp hq)) (CFSG.KC.BfsPin.canonK_pcomp cp cq) hs

theorem twoBD_eq_DD : twoBD = CertificateChecks.KernelCo1B.Tri2045.DD := by
  have h0 : xBar = CertificateChecks.KernelCo1B.Tri2045.φE CertificateChecks.KernelCo1B.Tri2045.xE :=
    strong0_eq.symm.trans CertificateChecks.KernelCo1B.Tri2045.perm0
  have h1 : yBar = CertificateChecks.KernelCo1B.Tri2045.φE CertificateChecks.KernelCo1B.Tri2045.yE :=
    strong1_eq.symm.trans CertificateChecks.KernelCo1B.Tri2045.perm1
  change Subgroup.closure {xBar, yBar} = _
  rw [h0, h1]

theorem ptStrong {j : ℕ} (hj : j < 6) : PtRep (LC.S j) (permOfArr 1365 twoBStrong[j]!) := by
  have h := strong_rep (j := j) hj
  rw [CertificateChecks.KernelCo1B.Tri2045.strong_facts.2 j hj,
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kSR j hj)] at h
  rw [CertificateChecks.KernelCo1B.Tri2045.strong_facts.2 j hj,
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kSR j hj)]
  exact ptRep_of_rep h

theorem centralizer_trivial : ∀ c : Pm, (∀ x ∈ twoBD, c * x = x * c) → c = 1 := by
  intro c hc
  have hq : c 0 = 0 := by
    by_contra hne
    have hne' : ((c 0 : Fin 1365) : ℕ) ≠ 0 := fun h0 => hne (Fin.ext h0)
    obtain ⟨j, hj, hj0, hjq⟩ := fixK_spec kFix _ (c 0).2 hne'
    have hP := ptStrong hj
    have hmem := strong_mem (j := j) hj
    have hfix : (permOfArr 1365 twoBStrong[j]!) 0 = 0 := by
      apply Fin.ext
      rw [← hP 0]
      exact hj0
    have hcomm := hc _ hmem
    have hfix' : (permOfArr 1365 twoBStrong[j]!) (c 0) = c 0 := by
      have := congrArg (fun p : Pm => p 0) hcomm
      simp only [Equiv.Perm.mul_apply] at this
      rw [← this, hfix]
    exact hjq (by rw [hP (c 0), hfix'])
  apply Equiv.ext
  intro z
  obtain ⟨g, hg, hgz⟩ := twoBD_exists_apply z
  have hcomm := hc g hg
  have := congrArg (fun p : Pm => p 0) hcomm
  simp only [Equiv.Perm.mul_apply, hq, hgz] at this
  simpa using this

theorem fact2N : (503193600 : ℕ).factorization 2 = 13 := by
  have h : (503193600 : ℕ) = 2 ^ 13 * 61425 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 61425)]
  simp

theorem ptX : PtRep (LC.S 0) xBar := by
  have := ptLC (j := 0) (by norm_num)
  simpa [gGen] using this

theorem ptY : PtRep (LC.S 1) yBar := by
  have := ptLC (j := 1) (by norm_num)
  simpa [gGen] using this

theorem ptYi : PtRep (LC.SI 1) yBar⁻¹ := by
  refine ptRep_inv ptY fun i hi => ?_
  have h := CFSG.KC.EnumSound.permOK_sound (n := 1365) (w := 11)
    (CFSG.KC.Pack.allN_spec kP 1 (by norm_num))
  rw [ap_eq_pg, ap_eq_pg]
  exact (h.2.2 i hi).2

theorem xBar_mem' : xBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert _ _)

theorem yBar_mem' : yBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem conj_mem {n : Pm} (hn : n ∈ Subgroup.normalizer (twoBD : Set Pm)) {x : Pm}
    (hx : x ∈ twoBD) : n * x * n⁻¹ ∈ twoBD :=
  (Subgroup.mem_normalizer_iff.1 hn x).1 hx

section Elts

variable {o τ : Pm}

theorem o_not_mem (hO : PtRep (PK 7) o) : o ∉ twoBD := by
  intro h
  have ha : o ∈ alternatingGroup (Fin 1365) :=
    CertificateChecks.KernelCo1B.Tri2045.DD_le_alt (by rw [← twoBD_eq_DD]; exact h)
  rw [Equiv.Perm.mem_alternatingGroup, sign_o hO] at ha
  exact absurd ha (by decide)

theorem o_ne_one (hO : PtRep (PK 7) o) : o ≠ 1 := fun h => o_not_mem hO (by rw [h]; exact one_mem _)

theorem o_conj (hO : PtRep (PK 7) o) (hOi : PtRep (PK 7) o⁻¹) {j : ℕ} (hj : j < 2) {g : Pm}
    (hg : PtRep (LC.S j) g) : o * g * o⁻¹ ∈ twoBD := by
  have hs := CFSG.KC.Pack.allN_spec (band_l kSiftO) j hj
  have := mem_of_pcomp hO (ptRep_pcomp hg hO) canO
    (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.Pack.allN_spec (band_r kCanO) j hj) canO) hs
  rw [o_inv hO hOi, mul_assoc]
  exact this

theorem o_mem_N (hO : PtRep (PK 7) o) (hOi : PtRep (PK 7) o⁻¹) :
    o ∈ Subgroup.normalizer (twoBD : Set Pm) :=
  mem_normalizer_of_conj rfl (o_conj hO hOi (j := 0) (by norm_num) ptX)
    (o_conj hO hOi (j := 1) (by norm_num) ptY)

theorem o_tau_mem (hO : PtRep (PK 7) o) (hT : PtRep (TAU 0) τ) : o * τ ∈ twoBD :=
  mem_of_pcomp hO hT canO (band_l kCanO) (band_r kSiftO)

theorem tau_mem_N (hO : PtRep (PK 7) o) (hOi : PtRep (PK 7) o⁻¹) (hT : PtRep (TAU 0) τ) :
    τ ∈ Subgroup.normalizer (twoBD : Set Pm) := by
  have e : τ = o * (o * τ) := by rw [← mul_assoc, o_sq hO hOi, one_mul]
  rw [e]
  exact mul_mem (o_mem_N hO hOi) (Subgroup.le_normalizer (o_tau_mem hO hT))

theorem tau_not_mem (hO : PtRep (PK 7) o) (hT : PtRep (TAU 0) τ) : τ ∉ twoBD := fun h =>
  o_not_mem hO (by
    have : o * τ * τ⁻¹ ∈ twoBD := mul_mem (o_tau_mem hO hT) (inv_mem h)
    simpa using this)

theorem tau_sq_mem (hO : PtRep (PK 7) o) (hOi : PtRep (PK 7) o⁻¹) (hT : PtRep (TAU 0) τ) :
    τ * τ ∈ twoBD := by
  have e : τ * τ = o * (o * τ) * o⁻¹ * (o * τ) := by
    rw [o_inv hO hOi]
    calc τ * τ = (o * o) * τ * (o * o) * τ := by rw [o_sq hO hOi]; group
      _ = o * (o * τ) * o * (o * τ) := by group
  rw [e]
  exact mul_mem (conj_mem (o_mem_N hO hOi) (o_tau_mem hO hT)) (o_tau_mem hO hT)

end Elts

@[expose] noncomputable def TT : Subgroup Pm := Subgroup.closure (gR '' Set.Iio 8)

@[expose] noncomputable def eT (k : ℕ) : Pm := treeE gRl TP TG 8 k

theorem gR_mem {j : ℕ} (hj : j < 8) : gR j ∈ twoBD :=
  mem_of_sift (rep_of_invEqK (CFSG.KC.Pack.allN_spec Cls27203.kInv j hj)).1
    (CFSG.KC.Pack.allN_spec (band_l Cls27203.kCan) j hj)
    (CFSG.KC.Pack.allN_spec (band_l (band_l Cls27203.kSift)) j hj)

theorem TT_le : TT ≤ twoBD := by
  rw [TT, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact gR_mem hj

theorem gRl_mem (l : ℕ) : gRl l ∈ TT := by
  unfold TT
  exact Subgroup.subset_closure ⟨_, land7_lt l, rfl⟩

theorem eT_mem (k : ℕ) : eT k ∈ TT := treeE_mem gRl_mem TP TG 8 k

theorem keyT_eq : ∀ k < 4096, keyT k = keyE (eT k) := treeK_spec ptT kTree

theorem TT_tree : (TT : Set Pm) = eT '' Set.Iio 4096 ∧ Nat.card TT = 4096 :=
  closure_eq_of_tree (γ := gR) (J := 8) (n := 4096) (e := eT)
    (fun k _ => eT_mem k) (by norm_num) (treeE_zero _ _ _ _)
    (fun i hi j hj => by
      obtain ⟨hc, hK⟩ := closK_spec kClos i hi j hj
      refine ⟨_, hc, twoBD_eq_of_keyE (TT_le (eT_mem _)) (mul_mem (gR_mem hj) (TT_le (eT_mem i)))
        ?_⟩
      rw [← keyT_eq _ hc, hK, keyT_eq i hi, kmap_keyE (ptT j)]
      have : gRl j = gR j := by
        unfold gRl
        congr 1
        change j &&& (2 ^ 3 - 1) = j
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_eq_of_lt hj
      rw [this])
    (fun i hi j hj h => sortedK_injOn kInc i hi j hj (by rw [keyT_eq i hi, keyT_eq j hj, h]))

theorem mem_TT_of_pts {g : Pm} (hg : g ∈ twoBD) {m : ℕ} (hm : m < 4096)
    (hb : ∀ x : Fin 1365, (x : ℕ) < 3 → (g x : ℕ) = kpt (keyT m) x) : g ∈ TT := by
  have : g = eT m := twoBD_eq_of_keyE hg (TT_le (eT_mem m))
    (keyE_eq_of_pts fun x hx => Fin.ext (by rw [hb x hx, keyT_eq m hm, kpt_keyE (eT m) hx]))
  rw [this]
  exact eT_mem m

theorem nrm_lt {j : ℕ} (hj : j < 8) : t12 MJ j < 4096 :=
  Nat.blt_eq.mp (band_l (CFSG.KC.Pack.allN_spec (band_l kNrm) j hj))

theorem nrm_pts {j : ℕ} (hj : j < 8) :
    ∀ b < 3, ap (TAU 0) (ap (RG j) (ap (TAU 1) b)) = kpt (keyT (t12 MJ j)) b :=
  ptsK_spec (band_r (CFSG.KC.Pack.allN_spec (band_l kNrm) j hj))

theorem nrm8_lt : t12 MJ 8 < 4096 := Nat.blt_eq.mp (band_l (band_r kNrm))

theorem nrm8_pts : ∀ b < 3, ap (TAU 0) (ap (TAU 0) b) = kpt (keyT (t12 MJ 8)) b :=
  ptsK_spec (band_r (band_r kNrm))

section Coset

variable {o τ : Pm}

theorem conj_pts (hT : PtRep (TAU 0) τ) (hTi : PtRep (TAU 1) τ⁻¹) {j : ℕ} (hj : j < 8) :
    ∀ x : Fin 1365, (x : ℕ) < 3 → ((τ * gR j * τ⁻¹) x : ℕ) = kpt (keyT (t12 MJ j)) x := by
  intro x hx
  rw [← nrm_pts hj x hx, hTi, ptRG hj, hT, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem sq_pts (hT : PtRep (TAU 0) τ) :
    ∀ x : Fin 1365, (x : ℕ) < 3 → ((τ * τ) x : ℕ) = kpt (keyT (t12 MJ 8)) x := by
  intro x hx
  rw [← nrm8_pts x hx, hT, hT, Equiv.Perm.mul_apply]

theorem tau_norm (hT : PtRep (TAU 0) τ) (hTi : PtRep (TAU 1) τ⁻¹)
    (hTN : τ ∈ Subgroup.normalizer (twoBD : Set Pm)) : ∀ x ∈ TT, τ * x * τ⁻¹ ∈ TT := by
  have hle : TT ≤ TT.comap (MulAut.conj τ).toMonoidHom := by
    rw [TT, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact mem_TT_of_pts (conj_mem hTN (gR_mem hj)) (nrm_lt hj) (conj_pts hT hTi hj)
  exact fun x hx => hle hx

theorem tau_sq_TT (hT : PtRep (TAU 0) τ) (h2 : τ * τ ∈ twoBD) : τ * τ ∈ TT :=
  mem_TT_of_pts h2 nrm8_lt (sq_pts hT)

theorem scan_conj (hO : PtRep (PK 7) o) (hOi : PtRep (PK 7) o⁻¹) (hT : PtRep (TAU 0) τ)
    {k : ℕ} (hk : k < 4096) (hsq : eT k * τ * (eT k * τ) = 1) :
    ∃ d ∈ twoBD, d * (eT k * τ) * d⁻¹ = o := by
  have hcs : ∀ x : Fin 1365, cosK gT TP TG 8 (TAU 0) k x = ((eT k * τ) x : ℕ) := fun x =>
    cosK_eq ptT hT TP TG 8 k x
  rcases recO_spec (CFSG.KC.Pack.allN_spec kScan k hk) with ⟨-, hb, hne⟩ | ⟨-, hall⟩
  · exfalso
    apply hne
    have e1 : cosK gT TP TG 8 (TAU 0) k (Nat.shiftRight (TR k) 1) =
        ((eT k * τ) ⟨Nat.shiftRight (TR k) 1, by omega⟩ : ℕ) :=
      hcs ⟨Nat.shiftRight (TR k) 1, by omega⟩
    rw [e1, hcs, ← Equiv.Perm.mul_apply, hsq]
    rfl
  · set W := Nat.shiftRight (TR k) 10
    set L := Nat.land (Nat.shiftRight (TR k) 2) 255
    have hwD : wordE xBar yBar⁻¹ W L ∈ twoBD := wordE_mem xBar_mem' (inv_mem yBar_mem') W L
    refine ⟨wordE xBar yBar⁻¹ W L, hwD, ?_⟩
    have hm : (o * wordE xBar yBar⁻¹ W L)⁻¹ * (wordE xBar yBar⁻¹ W L * (eT k * τ)) ∈
        twoBD := by
      have e2 : (o * wordE xBar yBar⁻¹ W L)⁻¹ * (wordE xBar yBar⁻¹ W L * (eT k * τ)) =
          (wordE xBar yBar⁻¹ W L)⁻¹ * (o⁻¹ * (wordE xBar yBar⁻¹ W L * eT k) * o⁻¹⁻¹) *
            (o⁻¹ * τ) := by
        group
      rw [e2]
      refine mul_mem (mul_mem (inv_mem hwD)
        (conj_mem (inv_mem (o_mem_N hO hOi)) (mul_mem hwD (TT_le (eT_mem k))))) ?_
      rw [o_inv hO hOi]
      exact o_tau_mem hO hT
    have hfix : ∀ x : Fin 1365, (x : ℕ) < 3 →
        ((o * wordE xBar yBar⁻¹ W L)⁻¹ * (wordE xBar yBar⁻¹ W L * (eT k * τ))) x = x := by
      intro x hx
      have h := hall x hx
      rw [hcs x, wpt_eq ptX ptYi W L ((eT k * τ) x), wpt_eq ptX ptYi W L x, hO] at h
      have h' : wordE xBar yBar⁻¹ W L ((eT k * τ) x) = o (wordE xBar yBar⁻¹ W L x) :=
        Fin.ext h
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h', ← Equiv.Perm.mul_apply o]
      simp
    have h1 := twoBD_eq_one hm (hfix 0 (by norm_num)) (hfix 1 (by norm_num))
      (hfix 2 (by norm_num))
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    group

theorem fusion_out (hO : PtRep (PK 7) o) (hOi : PtRep (PK 7) o⁻¹) (hT : PtRep (TAU 0) τ)
    (hTi : PtRep (TAU 1) τ⁻¹)
    (hN : Nat.card (Subgroup.normalizer (twoBD : Set Pm)) = 503193600) :
    ∀ s ∈ Subgroup.normalizer (twoBD : Set Pm), s * s = 1 → s ∉ twoBD →
      ∃ d ∈ twoBD, d * s * d⁻¹ = o := by
  classical
  have hTN := tau_mem_N hO hOi hT
  have hn := tau_norm hT hTi hTN
  have h2 := tau_sq_TT hT (tau_sq_mem hO hOi hT)
  let U := extT TT τ hn h2
  have hUcard : Nat.card U = 8192 := by
    rw [card_extT hn h2 fun h => tau_not_mem hO hT (TT_le h), TT_tree.2]
  have hUN : U ≤ Subgroup.normalizer (twoBD : Set Pm) := by
    rintro g (hg | hg)
    · exact Subgroup.le_normalizer (TT_le hg)
    · have e' : g = g * τ⁻¹ * τ := by group
      rw [e']
      exact mul_mem (Subgroup.le_normalizer (TT_le hg)) hTN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := Subgroup.normalizer (twoBD : Set Pm)
  let D' : Subgroup ↥N := twoBD.subgroupOf N
  have hD'card : Nat.card D' = Nat.card twoBD :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have hidx : D'.index = 2 := by
    have h := Subgroup.card_mul_index D'
    rw [hD'card, card_twoBD, hN] at h
    omega
  have hcos : ∀ n : ↥N, (n : Pm) ∉ twoBD → (n : Pm) * o ∈ twoBD := fun n hn =>
    (Subgroup.mul_mem_iff_of_index_two hidx (a := n) (b := ⟨o, o_mem_N hO hOi⟩)).2
      (iff_of_false hn (o_not_mem hO))
  let U' : Subgroup ↥N := U.subgroupOf N
  have hU'card : Nat.card U' = 8192 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv]
    exact hUcard
  let S : Sylow 2 ↥N := Sylow.ofCard U' (by rw [hU'card, hN, fact2N]; norm_num)
  let Q : Set ↥N := {w | (w : Pm) ∈ twoBD ∨ ∃ d ∈ twoBD, d * (w : Pm) * d⁻¹ = o}
  have hconj : ∀ n z, z ∈ Q → n * z * n⁻¹ ∈ Q := by
    rintro n z (hz | ⟨d, hd, hdz⟩)
    · exact Or.inl (conj_mem n.2 hz)
    · refine Or.inr ?_
      by_cases hn : (n : Pm) ∈ twoBD
      · refine ⟨d * (n : Pm)⁻¹, mul_mem hd (inv_mem hn), ?_⟩
        rw [← hdz]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      · have hc : (n : Pm) * d⁻¹ ∉ twoBD := fun h => hn (by
          have : (n : Pm) * d⁻¹ * d ∈ twoBD := mul_mem h hd
          simpa using this)
        let c : ↥N := n * ⟨d⁻¹, Subgroup.le_normalizer (inv_mem hd)⟩
        have hco : (c : Pm) * o ∈ twoBD := hcos c hc
        refine ⟨((c : Pm) * o)⁻¹, inv_mem hco, ?_⟩
        have hz : (z : Pm) = d⁻¹ * o * d := by rw [← hdz]; group
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz]
        change ((n : Pm) * d⁻¹ * o)⁻¹ * ((n : Pm) * (d⁻¹ * o * d) * (n : Pm)⁻¹) *
          ((n : Pm) * d⁻¹ * o)⁻¹⁻¹ = o
        group
  have hT : ∀ z ∈ (S : Subgroup ↥N), orderOf z = 2 → z ∈ Q := by
    intro z hzS hz2
    have hzU : (z : Pm) ∈ U := hzS
    have hzsq : (z : Pm) * z = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz2, pow_two] at this
      exact congrArg Subtype.val this
    rcases mem_extT.1 hzU with hzT | hzT
    · exact Or.inl (TT_le hzT)
    · have hz' : (z : Pm) * τ⁻¹ ∈ (TT : Set Pm) := hzT
      rw [TT_tree.1] at hz'
      obtain ⟨k, hk, hek⟩ := hz'
      have hzk : (z : Pm) = eT k * τ := by
        rw [hek]
        group
      rw [hzk] at hzsq
      refine Or.inr ?_
      rw [hzk]
      exact scan_conj hO hOi hT hk hzsq
  have hcov := cover_of_sylow S Q hconj hT
  intro s hs hssq hsD
  have hs1 : s ≠ 1 := fun h => hsD (by rw [h]; exact one_mem _)
  have hs2 : orderOf (⟨s, hs⟩ : ↥N) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using hssq)
    · exact fun h => hs1 (congrArg Subtype.val h)
  rcases hcov _ hs2 with h | h
  · exact absurd h hsD
  · exact h

theorem main_facts : (∀ c : Pm, (∀ x ∈ twoBD, c * x = x * c) → c = 1) ∧
    ∃ o : Pm, Rep 1365 oa o ∧ o * o = 1 ∧ o ≠ 1 ∧ o ∈ Subgroup.normalizer (twoBD : Set Pm) ∧
      o ∉ twoBD ∧
      (Nat.card (Subgroup.normalizer (twoBD : Set Pm)) = 503193600 →
        ∀ s ∈ Subgroup.normalizer (twoBD : Set Pm), s * s = 1 → s ∉ twoBD →
          ∃ d ∈ twoBD, d * s * d⁻¹ = o) := by
  obtain ⟨-, hO, hOi⟩ := rep_of_invEqK (band_l kInvO)
  obtain ⟨-, hT, hTi⟩ := rep_of_invEqK (band_r kInvO)
  exact ⟨centralizer_trivial, _, rep_oa, o_sq hO hOi, o_ne_one hO, o_mem_N hO hOi, o_not_mem hO,
    fusion_out hO hOi hT hTi⟩

end Coset

theorem outer_ok : (∀ c : Equiv.Perm (Fin 1365),
      (∀ x ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, c * x = x * c) → c = 1) ∧
    ∃ o : Equiv.Perm (Fin 1365), Rep 1365 oa o ∧ o * o = 1 ∧ o ≠ 1 ∧
      o ∈ Subgroup.normalizer
        (Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} : Set (Equiv.Perm (Fin 1365))) ∧
      o ∉ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧
      (Nat.card (Subgroup.normalizer
          (Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} :
            Set (Equiv.Perm (Fin 1365)))) = 503193600 →
        ∀ s ∈ Subgroup.normalizer
          (Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} : Set (Equiv.Perm (Fin 1365))),
          s * s = 1 → s ∉ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} →
            ∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, d * s * d⁻¹ = o) := by
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  rw [hX, hY]
  exact main_facts

end Main

end CertificateChecks.KernelG24.Out27204

end
