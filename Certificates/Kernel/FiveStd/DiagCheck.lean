module

public import Certificates.Kernel.FiveStd.DiagGlue
public import Certificates.Kernel.FiveStd.Syl
public import CFSG.Certificates.Kernel.FiveStdKSylConjSound

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

@[expose] def CentOf (g : E) : List E := Cs.filter fun x => commE x g

@[expose] def InvOf (g : E) : List E := (CentOf g).filter fun τ => ordE τ == 2 && τ != zE

@[expose] def AOf (g : E) : List E := (CentOf g).filter fun x => ordE x == 1 || ordE x == 5

theorem mem_CentOf {g x : E} : x ∈ CentOf g ↔ validE x = true ∧ mulE x g = mulE g x := by
  rw [CentOf, List.mem_filter, mem_Cs_iff, commE, beq_iff_eq]

theorem mem_AOf {g x : E} :
    x ∈ AOf g ↔ (validE x = true ∧ mulE x g = mulE g x) ∧ (ordE x = 1 ∨ ordE x = 5) := by
  rw [AOf, List.mem_filter, mem_CentOf, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]

theorem mem_InvOf {g x : E} :
    x ∈ InvOf g ↔ (validE x = true ∧ mulE x g = mulE g x) ∧ ordE x = 2 ∧ x ≠ zE := by
  rw [InvOf, List.mem_filter, mem_CentOf, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]

theorem nodup_AOf (g : E) : (AOf g).Nodup := (nodup_Cs.filter _).filter _

theorem s_conjE (c x : E) : (conjE c x).s = x.s := by
  unfold conjE
  rw [s_mulE, s_mulE, s_invE]
  cases c.s <;> cases x.s <;> rfl

theorem grp_inv {G : Type} [Group G] (v w r : G) (hv : v * r * v⁻¹ = r⁻¹) (hw : w * r * w⁻¹ = r⁻¹) :
    v⁻¹ * w * r = r * (v⁻¹ * w) := by
  have h1 : v⁻¹ * r⁻¹ * v = r := by rw [← hv]; group
  calc v⁻¹ * w * r = v⁻¹ * (w * r * w⁻¹) * w := by group
    _ = (v⁻¹ * r⁻¹ * v) * v⁻¹ * w := by rw [hw]; group
    _ = r * (v⁻¹ * w) := by rw [h1]; group

theorem grp_a {G : Type} [Group G] (c v r : G) (h : v * (c * r * c⁻¹) * v⁻¹ = (c * r * c⁻¹)⁻¹) :
    c⁻¹ * v * c⁻¹⁻¹ * r * (c⁻¹ * v * c⁻¹⁻¹)⁻¹ = r⁻¹ := by
  calc _ = c⁻¹ * (v * (c * r * c⁻¹) * v⁻¹) * c := by group
    _ = r⁻¹ := by rw [h]; group

theorem grp_b {G : Type} [Group G] (c v a : G)
    (h : c⁻¹ * v * c⁻¹⁻¹ * (c⁻¹ * a * c⁻¹⁻¹) * (c⁻¹ * v * c⁻¹⁻¹)⁻¹ = (c⁻¹ * a * c⁻¹⁻¹)⁻¹) :
    v * a * v⁻¹ = a⁻¹ := by
  calc v * a * v⁻¹ = c * (c⁻¹ * v * c⁻¹⁻¹ * (c⁻¹ * a * c⁻¹⁻¹) * (c⁻¹ * v * c⁻¹⁻¹)⁻¹) * c⁻¹ := by
        group
    _ = a⁻¹ := by rw [h]; group

section

variable {c r : E}

theorem comm_iff (hfact : Fact (Nat.Prime 5)) (hc : validE c = true) (hr : validE r = true)
    {x : E} (hx : validE x = true) :
    mulE x (conjE c r) = mulE (conjE c r) x ↔
      mulE (conjE (invE c) x) r = mulE r (conjE (invE c) x) := by
  have hM := Mat.model_ιF (F := ZMod 5)
  have hci := hM.valid_inv _ hc
  have hg := hM.valid_conjE hc hr
  have hψx := hM.valid_conjE hci hx
  constructor
  · intro h
    have := congrArg (conjE (invE c)) h
    rwa [cj_mul hM hci hx hg, cj_mul hM hci hg hx, cj_back hM hc hr] at this
  · intro h
    have := congrArg (conjE c) h
    rwa [cj_mul hM hc hψx hr, cj_mul hM hc hr hψx, cj_fwd hM hc hx] at this

theorem pow5_conj (hfact : Fact (Nat.Prime 5)) (hc : validE c = true) {x : E} (hx : validE x = true) :
    powE (conjE c x) 5 = oneE ↔ powE x 5 = oneE := by
  have hM := Mat.model_ιF (F := ZMod 5)
  constructor
  · intro h
    apply cj_inj hM hc (hM.valid_powE hx 5) hM.valid_one
    rw [← cj_pow hM hc hx, h, cj_one hM hc]
  · intro h
    rw [cj_pow hM hc hx, h, cj_one hM hc]

theorem body_rep {A B : List E} {v0 : E} (hRF : RepFacts r A B v0) (hc : validE c = true) :
    ((InvOf (conjE c r)).isEmpty ||
      ((AOf (conjE c r)).length == 25 && (AOf (conjE c r)).all inKK &&
      ((AOf (conjE c r)).all fun a => (AOf (conjE c r)).all fun b => inL (mulE a b) (AOf (conjE c r))) &&
      ((AOf (conjE c r)).all fun a => (CentOf (conjE c r)).all fun c' => inL (conjE c' a) (AOf (conjE c r))) &&
      (Cs.all fun v => conjE v (conjE c r) != invE (conjE c r) || !normK1 v ||
        (AOf (conjE c r)).all fun a => conjE v a == invE a) &&
      (InvOf (conjE c r)).all fun τ => eqL (CentOf (conjE c r))
        (prod2 (AOf (conjE c r)) [oneE, zE, τ, mulE zE τ]))) = true := by
  have hfact : Fact (Nat.Prime 5) := fact5
  have hM := Mat.model_ιF (F := ZMod 5)
  have hr := hRF.hr
  have hci := hM.valid_inv _ hc
  have hg := hM.valid_conjE hc hr
  set g := conjE c r with hgd
  have hCent : ∀ x, x ∈ CentOf g ↔ validE x = true ∧ conjE (invE c) x ∈ B := by
    intro x
    rw [mem_CentOf]
    exact ⟨fun ⟨hx, h⟩ => ⟨hx, (hRF.hcen _ (hM.valid_conjE hci hx)).1 ((comm_iff hfact hc hr hx).1 h)⟩,
      fun ⟨hx, h⟩ => ⟨hx, (comm_iff hfact hc hr hx).2 ((hRF.hcen _ (hM.valid_conjE hci hx)).2 h)⟩⟩
  have hAm : ∀ x, x ∈ AOf g ↔ validE x = true ∧ conjE (invE c) x ∈ A := by
    intro x
    rw [mem_AOf, ← mem_CentOf, hCent]
    constructor
    · rintro ⟨⟨hx, hb⟩, ho⟩
      have hp := (pow5_iff hM hx).1 ho
      exact ⟨hx, (hRF.hB _ hb).1 ((pow5_conj hfact hci hx).2 hp)⟩
    · rintro ⟨hx, ha⟩
      obtain ⟨hav, hac, hap, -, -⟩ := hRF.hA _ ha
      exact ⟨⟨hx, (hRF.hcen _ hav).1 hac⟩, (pow5_iff hM hx).2 ((pow5_conj hfact hci hx).1 hap)⟩
  have hAv : ∀ a ∈ A, validE a = true := fun a ha => (hRF.hA a ha).1
  rw [Bool.or_eq_true]
  right
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    rw [beq_iff_eq]
    have hnd2 : (A.map (conjE c)).Nodup :=
      hRF.hAnd.map_on fun a ha b hb h => cj_inj hM hc (hAv a ha) (hAv b hb) h
    have hperm : (AOf g).Perm (A.map (conjE c)) := by
      refine (List.perm_ext_iff_of_nodup (nodup_AOf g) hnd2).2 fun x => ?_
      rw [hAm, List.mem_map]
      constructor
      · rintro ⟨hx, ha⟩
        exact ⟨_, ha, cj_fwd hM hc hx⟩
      · rintro ⟨a, ha, rfl⟩
        refine ⟨hM.valid_conjE hc (hAv a ha), ?_⟩
        rw [cj_back hM hc (hAv a ha)]
        exact ha
    rw [hperm.length_eq, List.length_map, hRF.hAlen]
  ·
    rw [List.all_eq_true]
    intro a ha
    obtain ⟨hav, hψ⟩ := (hAm a).1 ha
    rw [← cj_fwd hM hc hav, inKK_conjE hc (hM.valid_conjE hci hav)]
    exact (hRF.hA _ hψ).2.2.2.1
  ·
    rw [List.all_eq_true]
    intro a ha
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨hav, hψa⟩ := (hAm a).1 ha
    obtain ⟨hbv, hψb⟩ := (hAm b).1 hb
    rw [inL, List.contains_iff_mem, hAm]
    refine ⟨hM.valid_mul _ _ hav hbv, ?_⟩
    rw [cj_mul hM hci hav hbv]
    exact (hRF.hA _ hψa).2.2.2.2 _ hψb
  ·
    rw [List.all_eq_true]
    intro a ha
    rw [List.all_eq_true]
    intro d hd
    obtain ⟨hav, hψa⟩ := (hAm a).1 ha
    obtain ⟨hdv, hψd⟩ := (hCent d).1 hd
    rw [inL, List.contains_iff_mem, hAm]
    refine ⟨hM.valid_conjE hdv hav, ?_⟩
    have : conjE (invE c) (conjE d a) = conjE (conjE (invE c) d) (conjE (invE c) a) := by
      have hψd' := hM.valid_conjE hci hdv
      have hψa' := hM.valid_conjE hci hav
      apply hM.inj _ _ (hM.valid_conjE hci (hM.valid_conjE hdv hav)) (hM.valid_conjE hψd' hψa')
      rw [hM.map_conjE hci (hM.valid_conjE hdv hav), hM.map_conjE hdv hav, hM.map_conjE hψd' hψa',
        hM.map_conjE hci hdv, hM.map_conjE hci hav]
      group
    rw [this]
    exact (hRF.hB _ hψd).2.1 _ hψa
  ·
    rw [List.all_eq_true]
    intro v hv
    have hvv := (mem_Cs_iff v).1 hv
    rw [Bool.or_eq_true, Bool.or_eq_true]
    by_cases h1 : conjE v g = invE g
    · by_cases h2 : normK1 v = true
      · right
        rw [List.all_eq_true]
        intro a ha
        rw [beq_iff_eq]
        obtain ⟨hav, hψa⟩ := (hAm a).1 ha
        set w := conjE (invE c) v with hwd
        have hw := hM.valid_conjE hci hvv
        have hwr : conjE w r = invE r := by
          apply hM.inj _ _ (hM.valid_conjE hw hr) (hM.valid_inv _ hr)
          have h1' := congrArg (Mat.ιF (ZMod 5)) h1
          rw [hM.map_conjE hvv hg, hM.map_inv _ hg, hgd, hM.map_conjE hc hr] at h1'
          rw [hM.map_conjE hw hr, hM.map_inv _ hr, hM.map_conjE hci hvv, hM.map_inv _ hc]
          exact grp_a _ _ _ h1'
        have hws : w.s = false := by rw [hwd, s_conjE]; exact s_of_normK1 hvv h2
        set b := mulE (invE v0) w with hbd
        have hbv : validE b = true := hM.valid_mul _ _ (hM.valid_inv _ hRF.hv0) hw
        have hbB : b ∈ B := by
          apply (hRF.hcen b hbv).1
          apply hM.inj _ _ (hM.valid_mul _ _ hbv hr) (hM.valid_mul _ _ hr hbv)
          rw [hM.map_mul _ _ hbv hr, hM.map_mul _ _ hr hbv, hbd, hM.map_mul _ _ (hM.valid_inv _ hRF.hv0) hw,
            hM.map_inv _ hRF.hv0]
          apply grp_inv
          · rw [← hM.map_conjE hRF.hv0 hr, hRF.hinv, hM.map_inv _ hr]
          · rw [← hM.map_conjE hw hr, hwr, hM.map_inv _ hr]
        have hvb : mulE v0 b = w := by
          apply hM.inj _ _ (hM.valid_mul _ _ hRF.hv0 hbv) hw
          rw [hM.map_mul _ _ hRF.hv0 hbv, hbd, hM.map_mul _ _ (hM.valid_inv _ hRF.hv0) hw,
            hM.map_inv _ hRF.hv0]
          group
        have hinvA := (hRF.hB b hbB).2.2 (by rw [hvb]; exact hws)
        have h3 := hinvA _ hψa
        rw [hvb] at h3
        apply hM.inj _ _ (hM.valid_conjE hvv hav) (hM.valid_inv _ hav)
        have h3' := congrArg (Mat.ιF (ZMod 5)) h3
        rw [hM.map_conjE hw (hM.valid_conjE hci hav), hM.map_inv _ (hM.valid_conjE hci hav),
          hM.map_conjE hci hvv, hM.map_conjE hci hav, hM.map_inv _ hc] at h3'
        rw [hM.map_conjE hvv hav, hM.map_inv _ hav]
        exact grp_b _ _ _ h3'
      · left
        right
        rw [Bool.not_eq_true] at h2
        rw [h2]
        rfl
    · left
      left
      rw [bne_iff_ne]
      exact h1
  ·
    rw [List.all_eq_true]
    intro τ hτ
    obtain ⟨⟨hτv, hτg⟩, hτ2, hτz⟩ := mem_InvOf.1 hτ
    obtain ⟨hττ, hτ1⟩ := (ord2_iff hM hτv).1 hτ2
    have hz : validE zE = true := by decide +kernel
    set τ' := conjE (invE c) τ with hτ'd
    have hτ'v := hM.valid_conjE hci hτv
    have hτ'B : τ' ∈ B := ((hCent τ).1 ((mem_CentOf).2 ⟨hτv, hτg⟩)).2
    have hτ'τ' : mulE τ' τ' = oneE := by
      rw [hτ'd, ← cj_mul hM hci hτv hτv, hττ, cj_one hM hci]
    have hτ'1 : τ' ≠ oneE := fun e => hτ1 (by rw [← cj_fwd hM hc hτv, ← hτ'd, e, cj_one hM hc])
    have hτ'z : τ' ≠ zE := fun e => hτz (by rw [← cj_fwd hM hc hτv, ← hτ'd, e, cj_z hc])
    unfold eqL subL
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    constructor
    · intro x hx
      rw [inL, List.contains_iff_mem]
      obtain ⟨hxv, hψx⟩ := (hCent x).1 hx
      obtain ⟨v', hv', hm⟩ := hRF.hdv τ' hτ'B hτ'τ' hτ'1 hτ'z _ hψx
      have hv'v : validE v' = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
        rcases hv' with rfl | rfl | rfl | rfl
        · exact hM.valid_one
        · exact hz
        · exact hτ'v
        · exact hM.valid_mul _ _ hz hτ'v
      have hmv := hAv _ hm
      refine List.mem_flatMap.2 ⟨conjE c (mulE (conjE (invE c) x) (invE v')), ?_,
        List.mem_map.2 ⟨conjE c v', ?_, ?_⟩⟩
      · rw [hAm]
        exact ⟨hM.valid_conjE hc hmv, by rw [cj_back hM hc hmv]; exact hm⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv' ⊢
        rcases hv' with rfl | rfl | rfl | rfl
        · exact Or.inl (cj_one hM hc)
        · exact Or.inr (Or.inl (cj_z hc))
        · exact Or.inr (Or.inr (Or.inl (cj_fwd hM hc hτv)))
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [cj_mul hM hc hz hτ'v, cj_z hc, cj_fwd hM hc hτv]
      · rw [← cj_mul hM hc hmv hv'v]
        have : mulE (mulE (conjE (invE c) x) (invE v')) v' = conjE (invE c) x := by
          have hψxv := hM.valid_conjE hci hxv
          apply hM.inj _ _ (hM.valid_mul _ _ hmv hv'v) hψxv
          rw [hM.map_mul _ _ hmv hv'v, hM.map_mul _ _ hψxv (hM.valid_inv _ hv'v), hM.map_inv _ hv'v]
          group
        rw [this, cj_fwd hM hc hxv]
    · intro y hy
      rw [inL, List.contains_iff_mem]
      obtain ⟨a, ha, hy'⟩ := List.mem_flatMap.1 hy
      obtain ⟨v, hvV, rfl⟩ := List.mem_map.1 hy'
      obtain ⟨⟨hav, hag⟩, -⟩ := mem_AOf.1 ha
      have hvg : validE v = true ∧ mulE v g = mulE g v := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hvV
        rcases hvV with rfl | rfl | rfl | rfl
        · refine ⟨hM.valid_one, ?_⟩
          rw [oneE_mulE hg, mulE_oneE hg]
        · exact ⟨hz, (z_central hg).symm⟩
        · exact ⟨hτv, hτg⟩
        · refine ⟨hM.valid_mul _ _ hz hτv, ?_⟩
          apply hM.inj _ _ (hM.valid_mul _ _ (hM.valid_mul _ _ hz hτv) hg)
            (hM.valid_mul _ _ hg (hM.valid_mul _ _ hz hτv))
          have h1 := congrArg (Mat.ιF (ZMod 5)) (z_central hg)
          have h2 := congrArg (Mat.ιF (ZMod 5)) hτg
          rw [hM.map_mul _ _ hg hz, hM.map_mul _ _ hz hg] at h1
          rw [hM.map_mul _ _ hτv hg, hM.map_mul _ _ hg hτv] at h2
          rw [hM.map_mul _ _ (hM.valid_mul _ _ hz hτv) hg, hM.map_mul _ _ hg (hM.valid_mul _ _ hz hτv),
            hM.map_mul _ _ hz hτv, mul_assoc, h2, ← mul_assoc, ← h1, mul_assoc]
      obtain ⟨hvv, hvg'⟩ := hvg
      rw [mem_CentOf]
      refine ⟨hM.valid_mul _ _ hav hvv, ?_⟩
      apply hM.inj _ _ (hM.valid_mul _ _ (hM.valid_mul _ _ hav hvv) hg)
        (hM.valid_mul _ _ hg (hM.valid_mul _ _ hav hvv))
      have h1 := congrArg (Mat.ιF (ZMod 5)) hag
      have h2 := congrArg (Mat.ιF (ZMod 5)) hvg'
      rw [hM.map_mul _ _ hav hg, hM.map_mul _ _ hg hav] at h1
      rw [hM.map_mul _ _ hvv hg, hM.map_mul _ _ hg hvv] at h2
      rw [hM.map_mul _ _ (hM.valid_mul _ _ hav hvv) hg, hM.map_mul _ _ hg (hM.valid_mul _ _ hav hvv),
        hM.map_mul _ _ hav hvv, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem body_noinv {B : List E} (hNF : NoInvFacts r B) (hc : validE c = true) :
    (InvOf (conjE c r)).isEmpty = true := by
  have hfact : Fact (Nat.Prime 5) := fact5
  have hM := Mat.model_ιF (F := ZMod 5)
  have hr := hNF.hr
  have hci := hM.valid_inv _ hc
  rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
  intro τ hτ
  obtain ⟨⟨hτv, hτg⟩, hτ2, hτz⟩ := mem_InvOf.1 hτ
  obtain ⟨hττ, hτ1⟩ := (ord2_iff hM hτv).1 hτ2
  have hτ'B := (hNF.hcen _ (hM.valid_conjE hci hτv)).1 ((comm_iff hfact hc hr hτv).1 hτg)
  have hτ'τ' : mulE (conjE (invE c) τ) (conjE (invE c) τ) = oneE := by
    rw [← cj_mul hM hci hτv hτv, hττ, cj_one hM hci]
  rcases hNF.hB _ hτ'B hτ'τ' with e | e
  · exact hτ1 (by rw [← cj_fwd hM hc hτv, e, cj_one hM hc])
  · exact hτz (by rw [← cj_fwd hM hc hτv, e, cj_z hc])

end

theorem ordE_oneE : ordE oneE = 1 := by rw [← ordK_codeE, codeE_oneE]; decide +kernel

theorem rp_ord3 : ordK (RP.getD 3 0) = 3 ∧ ordK (RP.getD 4 0) = 3 := by decide +kernel

theorem r1_codes : (ppE (decE 29501) (decE 78797) 5 5).map codeE = ppK 29501 78797 5 5 := by
  rw [map_ppE, codeE_decE (by norm_num), codeE_decE (by norm_num)]

theorem conj_rep {g : E} (hg : validE g = true) (h5 : ordE g = 5) :
    ∃ k < 3, ∃ c, validE c = true ∧ g = conjE c (decE (RP.getD k 0)) := by
  have hfact : Fact (Nat.Prime 5) := fact5
  have hM := Mat.model_ιF (F := ZMod 5)
  have hgen := (clsOK_spec (clsF_eq 0 ▸ cls_ok 0 (by norm_num))).1
  have hK := card_vSub hM (fun l => decE (f20 G l))
    (fun l hl => ⟨valid_decE (hgen l hl).1, codeE_decE (validK_lt (hgen l hl).1)⟩) tree_all
  obtain ⟨hx, hy, hxy, hxp, hyp, -, -, hall⟩ := syl_sound syl5
  have hnd : (ppE (decE 29501) (decE 78797) 5 5).Nodup := List.Nodup.of_map codeE (r1_codes ▸ r1_nodup)
  have hgp := (pow5_iff hM hg).1 (Or.inr h5)
  obtain ⟨c, hc, i, hi, j, hj, hgc⟩ :=
    conj_into_pp hM hK (p := 5) (by norm_num) (by norm_num) hx hy hxy hxp hyp hnd hg hgp
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    by_contra hne
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
    have : g = oneE := by
      rw [hgc]
      change conjE c (mulE oneE oneE) = oneE
      rw [oneE_mulE hM.valid_one, cj_one hM hc]
    rw [this, ordE_oneE] at h5
    exact absurd h5 (by norm_num)
  obtain ⟨k, hk, j', hj', he⟩ := hall i hi j hj hij
  have hhv := hM.valid_mul _ _ (hM.valid_powE hx i) (hM.valid_powE hy j)
  have hmem : mulE (powE (decE 29501) i) (powE (decE 78797) j) ∈
      decL (fun j => oCode (f96 (OR.getD k 0) j)) (OM.getD k 0) :=
    mem_decL.2 ⟨j', hj', by rw [he, decE_codeE]⟩
  obtain ⟨hrk, horb, -⟩ := cls_glue k hk
  obtain ⟨c', hc', hce⟩ := (horb _ hhv).2 hmem
  have hg' : g = conjE (mulE c c') (decE (RP.getD k 0)) := by
    rw [hgc, ← hce, cj_cj hM hc hc' hrk]
  have hk3 : k < 3 := by
    by_contra hk3
    have h3 : ordE (decE (RP.getD k 0)) = 3 := by
      rw [← ordK_codeE, codeE_decE (validK_lt ((clsOK_spec (clsF_eq k ▸ cls_ok k hk)).2.1))]
      interval_cases k
      · exact rp_ord3.1
      · exact rp_ord3.2
    have := ord_conj hM (hM.valid_mul _ _ hc hc') hrk h3 (by norm_num)
    rw [← hg', h5] at this
    exact absurd this (by norm_num)
  exact ⟨k, hk3, _, hM.valid_mul _ _ hc hc', hg'⟩

theorem diag_check : diagCheck = true := by
  unfold diagCheck
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨hgC, h5⟩ := List.mem_filter.1 (List.mem_filter.1 hg).1
  rw [beq_iff_eq] at h5
  obtain ⟨k, hk, c, hc, rfl⟩ := conj_rep ((mem_Cs_iff g).1 hgC) h5
  interval_cases k
  · exact body_rep (rep_facts 0 (by norm_num)) hc
  · exact body_rep (rep_facts 1 (by norm_num)) hc
  · change ((InvOf _).isEmpty || _) = true
    rw [body_noinv noinv_facts hc]
    rfl

end CertificateChecks.FiveStd

end
