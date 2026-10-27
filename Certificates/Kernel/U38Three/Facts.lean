module

public import Certificates.Kernel.U38Three.Glue
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Model3
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38Three

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.RankThree.PartOne U38Sylow U38Three
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K

theorem cubeOne_iff' {a : Array ℕ} (ha : validA 513 a = true) :
    cubeOne a = true ↔ permOfArr 513 a ^ 3 = 1 := by
  rw [pow_three]
  exact eqA_iff (rep_compA (rep_of_validA ha) (rep_compA (rep_of_validA ha) (rep_of_validA ha))) rep_idA

theorem commAt_iff' {a b : Array ℕ} (ha : validA 513 a = true) (hb : validA 513 b = true) :
    commAt a b = true ↔ permOfArr 513 a * permOfArr 513 b = permOfArr 513 b * permOfArr 513 a :=
  eqA_iff (rep_compA (rep_of_validA ha) (rep_of_validA hb)) (rep_compA (rep_of_validA hb) (rep_of_validA ha))

theorem perm_apply_eq' {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) {i : ℕ} (hi : i < n)
    {v : ℕ} (hv : t[i]! = v) (hvn : v < n) : g ⟨i, hi⟩ = ⟨v, hvn⟩ :=
  Fin.ext ((ht.apply hi).symm.trans hv)

theorem permsA_pair' (n : ℕ) (a b : Array ℕ) : permsA n #[a, b] = {permOfArr n a, permOfArr n b} := by
  ext x
  simp only [permsA, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by simpa using hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩

theorem d0_valid : validA 513 d0 = true := d0_facts.1

theorem s0 : siftA 513 (rawLevels 513 strong1 base1) base1 0 d0 = true ∧ fix01 d0 = true := by
  rw [d0_eq]
  exact sift1_fix (by norm_num)

theorem fix_of {t : Array ℕ} (hv : validA 513 t = true) (hf : fix01 t = true) :
    permOfArr 513 t 0 = 0 ∧ permOfArr 513 t 1 = 1 := by
  simp only [fix01, Bool.and_eq_true, beq_iff_eq] at hf
  exact ⟨perm_apply_eq' (rep_of_validA hv) (by norm_num) hf.1 (by norm_num),
    perm_apply_eq' (rep_of_validA hv) (by norm_num) hf.2 (by norm_num)⟩

theorem la_valid : validA 513 la = true := by rw [la_eq]; exact validA_of (pF (by norm_num))

theorem lb_valid : validA 513 lb = true := by rw [lb_eq]; exact validA_of (pF (by norm_num))

theorem elem_fact {x : Equiv.Perm (Fin 513)} (hx : x ∈ Subgroup.closure (permsA 513 hGens))
    (h3 : x ^ 3 = 1) (h1 : x ≠ 1) (h2 : x ≠ permOfArr 513 d0)
    (h4 : x ≠ permOfArr 513 d0 * permOfArr 513 d0) :
    x * permOfArr 513 d0 = permOfArr 513 d0 * x ∧
      {y | y ∈ Subgroup.closure (permsA 513 hGens) ∧ y ^ 3 = 1 ∧ x * y = y * x}.ncard ≤ 9 := by
  classical
  obtain ⟨hmem, -, hval⟩ := enumOK_spec KernelU38Q.hps enumH.1
  set pts := (hCert ()).pts with hpts
  have D0_rep : Rep 513 d0 (permOfArr 513 d0) := rep_of_validA d0_valid
  obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
  have hcube : cubeOne pts[i]! = true := (cubeOne_iff' (hval i hi)).2 h3
  have hics : i ∈ cubeIdx pts := by
    simp only [cubeIdx, List.mem_filter, List.mem_range]
    exact ⟨hi, hcube⟩
  have hall : ∀ k ∈ cubeIdx pts, (eqA 513 pts[k]! (idA 513) || eqA 513 pts[k]! d0 ||
      eqA 513 pts[k]! (compA 513 d0 d0) ||
      (commAt pts[k]! d0 && decide (((cubeIdx pts).filter fun j => commAt pts[k]! pts[j]!).length ≤ 9))) =
        true :=
    List.all_eq_true.1 hElem_true
  have hck' := hall i hics
  have hx1 : eqA 513 pts[i]! (idA 513) = false := by
    rw [Bool.eq_false_iff]
    exact fun h => h1 ((eqA_iff (rep_of_validA (hval i hi)) rep_idA).1 h)
  have hx2 : eqA 513 pts[i]! d0 = false := by
    rw [Bool.eq_false_iff]
    exact fun h => h2 ((eqA_iff (rep_of_validA (hval i hi)) D0_rep).1 h)
  have hx3 : eqA 513 pts[i]! (compA 513 d0 d0) = false := by
    rw [Bool.eq_false_iff]
    exact fun h => h4 ((eqA_iff (rep_of_validA (hval i hi)) (rep_compA D0_rep D0_rep)).1 h)
  simp only [hx1, hx2, hx3, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hck'
  obtain ⟨hcd, hlen⟩ := hck'
  refine ⟨(commAt_iff' (hval i hi) d0_valid).1 hcd, ?_⟩
  set F := (cubeIdx pts).filter fun j => commAt pts[i]! pts[j]! with hF
  have hmemF : ∀ j, j ∈ F ↔ j < pts.size ∧ cubeOne pts[j]! = true ∧ commAt pts[i]! pts[j]! = true := by
    intro j
    simp only [hF, cubeIdx, List.mem_filter, List.mem_range, and_assoc]
  set Sf := F.toFinset.image fun j => permOfArr 513 pts[j]! with hSf
  have hSf9 : Sf.card ≤ 9 := Finset.card_image_le.trans ((List.toFinset_card_le _).trans hlen)
  have hsub : {y | y ∈ Subgroup.closure (permsA 513 hGens) ∧ y ^ 3 = 1 ∧
      permOfArr 513 pts[i]! * y = y * permOfArr 513 pts[i]!} ⊆ ↑Sf := by
    rintro y ⟨hyH, hy3, hyc⟩
    obtain ⟨j, hj, rfl⟩ := (hmem y).1 hyH
    rw [Finset.mem_coe, hSf, Finset.mem_image]
    refine ⟨j, ?_, rfl⟩
    rw [List.mem_toFinset, hmemF]
    exact ⟨hj, (cubeOne_iff' (hval j hj)).2 hy3, (commAt_iff' (hval i hi) (hval j hj)).2 hyc⟩
  calc _ ≤ (↑Sf : Set (Equiv.Perm (Fin 513))).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = Sf.card := Set.ncard_coe_finset Sf
    _ ≤ 9 := hSf9

theorem L_le_X :
    Subgroup.closure (permsA 513 #[la, lb]) ≤
      Subgroup.centralizer ({permOfArr 513 d0} : Set (Equiv.Perm (Fin 513))) ⊓ X' := by
  rw [permsA_pair', Subgroup.closure_le]
  have s3 := siftX_of (j := 3) (by norm_num) (by norm_num)
  have s4 := siftX_of (j := 4) (by norm_num) (by norm_num)
  rw [← la_eq] at s3
  rw [← lb_eq] at s4
  rintro _ (rfl | rfl)
  · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
      ((commAt_iff' la_valid d0_valid).1 comm_l.1), sift3_mem (rep_of_validA la_valid) s3⟩
  · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
      ((commAt_iff' lb_valid d0_valid).1 comm_l.2), sift3_mem (rep_of_validA lb_valid) s4⟩

theorem cent_eq : Subgroup.closure (permsA 513 cGens) =
      Subgroup.centralizer ({permOfArr 513 d0} : Set (Equiv.Perm (Fin 513))) ⊓ X' ∧
    Nat.card (Subgroup.closure (permsA 513 cGens)) = 1512 := by
  obtain ⟨h1, h2⟩ := centralizer_card_of_centOKP (n := 513) (by norm_num) hk3 base3L_nodup chain3_ok
    (rep_of_validA d0_valid) KernelU38Q.hps cent_true
  refine ⟨h1.trans ?_, h2⟩
  rw [← Q3_group]
  rfl

theorem le_normalizer_L :
    Subgroup.centralizer ({permOfArr 513 d0} : Set (Equiv.Perm (Fin 513))) ⊓ X' ≤
      Subgroup.normalizer (Subgroup.closure (permsA 513 #[la, lb]) : Set (Equiv.Perm (Fin 513))) := by
  set L := Subgroup.closure (permsA 513 #[la, lb]) with hL
  have L_eq : L = Subgroup.closure {permOfArr 513 la, permOfArr 513 lb} := by rw [hL, permsA_pair']
  rw [← cent_eq.1, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hall := allLt_spec mem_true hk
  simp only [Bool.and_eq_true] at hall
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hall
  have hcv : validA 513 cGens[k]! = true := enumOK_gens_valid enumC.1 hk
  have hmemL : ∀ {t : Array ℕ} {T : Equiv.Perm (Fin 513)}, Rep 513 t T → memPts (lCert ()) t = true → T ∈ L :=
    fun ht hm => enumOK_mem_of_any KernelU38Q.hps enumL.1 ht hm
  have La_rep := rep_of_validA la_valid
  have Lb_rep := rep_of_validA lb_valid
  set c := permOfArr 513 cGens[k]! with hc
  have hcLa : c * permOfArr 513 la * c⁻¹ ∈ L := hmemL (rep_conjA hcv La_rep) h1
  have hcLb : c * permOfArr 513 lb * c⁻¹ ∈ L := hmemL (rep_conjA hcv Lb_rep) h2
  have hcLa' : c⁻¹ * permOfArr 513 la * c ∈ L := hmemL (rep_conjInvA hcv La_rep) h3
  have hcLb' : c⁻¹ * permOfArr 513 lb * c ∈ L := hmemL (rep_conjInvA hcv Lb_rep) h4
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [L_eq] at hh
    exact conj_closure_mem _ L c (by rintro s (rfl | rfl); exacts [hcLa, hcLb]) h hh
  · intro hh
    rw [L_eq] at hh
    have := conj_closure_mem _ L c⁻¹ (by
      rintro s (rfl | rfl)
      · rw [inv_inv]; exact hcLa'
      · rw [inv_inv]; exact hcLb') _ hh
    have heq : c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ = h := by group
    rwa [heq] at this

theorem L_card : Nat.card (Subgroup.closure (permsA 513 #[la, lb])) = 504 := by
  rw [(enumOK_spec KernelU38Q.hps enumL.1).2.1, szL]

theorem L_simple : IsSimpleGroup (Subgroup.closure (permsA 513 #[la, lb])) := by
  have hPs : IsSimpleGroup (Subgroup.closure (permsA 9 #[pa, pb])) := p_simple
  have hpa : pa = unpack 9 4 (PE.G 0) := pGens_get (k := 0) (by norm_num)
  have hpb : pb = unpack 9 4 (PE.G 1) := pGens_get (k := 1) (by norm_num)
  have hpav : validA 9 pa = true := by
    rw [hpa]
    exact validA_of (permGP 0 (by rw [pnums.2.1]; norm_num))
  have hpbv : validA 9 pb = true := by
    rw [hpb]
    exact validA_of (permGP 1 (by rw [pnums.2.1]; norm_num))
  have hPa := rep_of_validA hpav
  have hPb := rep_of_validA hpbv
  have La_rep := rep_of_validA la_valid
  have Lb_rep := rep_of_validA lb_valid
  have hlab : ∀ j : Fin 9, la[(j : ℕ)]! = pa[(j : ℕ)]! ∧ lb[(j : ℕ)]! = pb[(j : ℕ)]! := fun j => by
    have e := Orb.allN_iff.1 ch810201LP j j.2
    simp only [Bool.and_eq_true] at e
    rw [la_eq, lb_eq, hpa, hpb, Orb.unpack_get (by omega : (j : ℕ) < 513),
      Orb.unpack_get (by omega : (j : ℕ) < 513), Orb.unpack_get j.2, Orb.unpack_get j.2]
    exact ⟨Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2⟩
  have h9 : 9 ≤ 513 := by norm_num
  refine CFSG.Sporadic.FischerOddCore.isSimpleGroup_of_famHom (MonoidHom.id _) (s := Fin.castLE h9)
    (Fin.castLE_injective h9) (a := permOfArr 513 la) (b := permOfArr 513 lb)
    (pa := permOfArr 9 pa) (pb := permOfArr 9 pb) (fun j => ?_) (fun j => ?_) (by rw [permsA_pair'])
    (by rw [permsA_pair']) ?_ hPs
  · apply Fin.ext
    rw [Fin.coe_castLE, ← hPa j, MonoidHom.id_apply, ← La_rep (Fin.castLE h9 j), Fin.coe_castLE]
    exact (hlab j).1.symm
  · apply Fin.ext
    rw [Fin.coe_castLE, ← hPb j, MonoidHom.id_apply, ← Lb_rep (Fin.castLE h9 j), Fin.coe_castLE]
    exact (hlab j).2.symm
  · have hcP : Nat.card (Subgroup.closure (permsA 9 pGens)) = 504 := by
      rw [(enumOK_spec hps9 enumP.1).2.1, szP]
    rw [L_card]
    exact hcP.symm

theorem H_le : Subgroup.closure (permsA 513 hGens) ≤
    U38G ⊓ MulAction.stabilizer (Equiv.Perm (Fin 513)) (0 : Fin 513) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 513)) (1 : Fin 513) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' := allLt_spec genH_true hk
  simp only [Bool.and_eq_true] at hk'
  have hv := enumOK_gens_valid enumH.1 hk
  have hf := fix_of hv hk'.2
  simp only [SetLike.mem_coe, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  exact ⟨⟨mem_U38G_of_sift1 hv hk'.1, hf.1⟩, hf.2⟩

open Certificates in
open CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Item434U38 in
theorem facts :
    (permOfArr 513 U38Three.d0 0 = 0 ∧ permOfArr 513 U38Three.d0 1 = 1) ∧
    permOfArr 513 U38Three.d0 ^ 3 = 1 ∧ permOfArr 513 U38Three.d0 ≠ 1 ∧
    permOfArr 513 U38Three.d0 ∈ U38G ∧
    Subgroup.closure (permsA 513 U38Three.hGens) ≤
      U38G ⊓ MulAction.stabilizer (Equiv.Perm (Fin 513)) (0 : Fin 513) ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 513)) (1 : Fin 513) ∧
    Nat.card (Subgroup.closure (permsA 513 U38Three.hGens)) = 378 ∧
    (∀ x ∈ Subgroup.closure (permsA 513 U38Three.hGens), x ^ 3 = 1 → x ≠ 1 →
      x ≠ permOfArr 513 U38Three.d0 → x ≠ permOfArr 513 U38Three.d0 * permOfArr 513 U38Three.d0 →
      x * permOfArr 513 U38Three.d0 = permOfArr 513 U38Three.d0 * x ∧
        {y | y ∈ Subgroup.closure (permsA 513 U38Three.hGens) ∧ y ^ 3 = 1 ∧ x * y = y * x}.ncard ≤ 9) ∧
    Subgroup.closure (permsA 513 #[U38Three.la, U38Three.lb]) ≤
      Subgroup.centralizer ({permOfArr 513 U38Three.d0} : Set (Equiv.Perm (Fin 513))) ⊓ X' ∧
    Nat.card (Subgroup.closure (permsA 513 #[U38Three.la, U38Three.lb])) = 504 ∧
    IsSimpleGroup (Subgroup.closure (permsA 513 #[U38Three.la, U38Three.lb])) ∧
    Subgroup.centralizer ({permOfArr 513 U38Three.d0} : Set (Equiv.Perm (Fin 513))) ⊓ X' ≤
      Subgroup.normalizer (Subgroup.closure (permsA 513 #[U38Three.la, U38Three.lb]) :
        Set (Equiv.Perm (Fin 513))) ∧
    Nat.card ↥(Subgroup.centralizer ({permOfArr 513 U38Three.d0} : Set (Equiv.Perm (Fin 513))) ⊓ X') =
      1512 := by
  refine ⟨fix_of d0_valid s0.2, (cubeOne_iff' d0_valid).1 d0_facts.2.1, fun h => ?_,
    mem_U38G_of_sift1 d0_valid s0.1, H_le, ?_, fun x hx h3 h1 h2 h4 => elem_fact hx h3 h1 h2 h4,
    L_le_X, L_card, L_simple, le_normalizer_L, by rw [← cent_eq.1, cent_eq.2]⟩
  · have h' : eqA 513 d0 (idA 513) = true := (eqA_iff (rep_of_validA d0_valid) rep_idA).2 h
    rw [d0_facts.2.2] at h'
    exact Bool.false_ne_true h'
  · rw [(enumOK_spec KernelU38Q.hps enumH.1).2.1, szH]

end CertificateChecks.KernelU38Three

end
