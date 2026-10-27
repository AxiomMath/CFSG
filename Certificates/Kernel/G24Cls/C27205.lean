module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundWord
public import Certificates.Kernel.G24Cls.Chk27205
public import Certificates.Kernel.G24Cls.C26992
public import CFSG.Certificates.Kernel.G24RigidSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutClasses

public section

set_option maxRecDepth 400000
set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelG24.Rigid27205

open CFSG.KC.Enum CFSG.KC.Pack CFSG.KC.G24Key CFSG.KC.G24Rigid CertificateChecks.KernelG24.Tri27206
  CertificateChecks.KernelG24.Cls27203 CertificateChecks.KernelG24.Dih26992
  CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2 CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Induction.AutBound

theorem land15_lt (l : ℕ) : Nat.land l 15 < 16 := by
  change l &&& (2 ^ 4 - 1) < 16
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem ncard_le_countP' {S : Set Pm} {f : ℕ → Pm} {n : ℕ} (p : ℕ → Bool)
    (h : ∀ z ∈ S, ∃ k < n, p k = true ∧ f k = z) :
    S.ncard ≤ (List.range n).countP p := by
  classical
  let T : Finset ℕ := ((List.range n).filter p).toFinset
  have hsub : S ⊆ f '' (T : Set ℕ) := by
    intro z hz
    obtain ⟨k, hk, hpk, rfl⟩ := h z hz
    exact ⟨k, by simp [T, hk, hpk], rfl⟩
  have hT : T.card = (List.range n).countP p := by
    rw [List.countP_eq_length_filter]
    exact List.toFinset_card_of_nodup ((List.nodup_range).filter _)
  calc S.ncard ≤ (f '' (T : Set ℕ)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (T : Set ℕ).ncard := Set.ncard_image_le (Finset.finite_toSet _)
    _ = (List.range n).countP p := by rw [Set.ncard_coe_finset, hT]

theorem tst_range : ∀ i, 1 ≤ i → i < 4 → ∀ t ∈ tst i, (∀ l ∈ t.1, l ≤ i) ∧ 0 < t.2 := by
  intro i h1 h4
  interval_cases i <;> decide

theorem tst_one_two : ∀ t ∈ tst 1, t ∈ tst 2 := by decide

section Main


theorem gens_ex : ∀ j < 16, ∃ g ∈ twoBD, PtRep (SG j) g := by
  have k := kGen
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨⟨k0, k1⟩, kslp⟩, -⟩ := k
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h2
    · refine ⟨xBar, hxD, fun x => ?_⟩
      rw [ptEqK_spec k0 x x.2]
      exact ptX x
    · refine ⟨yBar, hyD, fun x => ?_⟩
      rw [ptEqK_spec k1 x x.2]
      exact ptY x
    · obtain ⟨ha, hb, hp⟩ := slpK_spec kslp j h2 hj
      obtain ⟨ga, hgaD, hga⟩ := ih _ ha (by omega)
      obtain ⟨gb, hgbD, hgb⟩ := ih _ hb (by omega)
      refine ⟨ga * gb, mul_mem hgaD hgbD, fun x => ?_⟩
      rw [hp x x.2, hgb x, hga]
      rfl

theorem sepD : ∀ u ∈ twoBD, (∀ x : Fin 1365, (x : ℕ) < 3 → u x = x) → u = 1 :=
  fun u hu h => twoBD_eq_one hu (h 0 (by decide)) (h 1 (by decide)) (h 2 (by decide))

theorem rigid_facts :
    ∃ b : ℕ → Pm, ∃ tests : ℕ → List (List ℕ × ℕ), Rep 1365 tAa (b 0) ∧
      (∀ j, ∃ d ∈ twoBD, b j = d * b 0 * d⁻¹) ∧ Subgroup.closure (b '' {j | j < 4}) = twoBD ∧
      ∀ i, 1 ≤ i → i < 4 →
        (∀ t ∈ tests i, (∀ l ∈ t.1, l ≤ i) ∧ 0 < t.2 ∧ orderOf (tupleWord b (b i) t.1) = t.2) ∧
        {z | (∃ d ∈ twoBD, z = d * b 0 * d⁻¹) ∧
          ∀ t ∈ tests i, orderOf (tupleWord b z t.1) = t.2}.ncard ≤
          if i = 1 then 1024 else if i = 2 then 60 else 2 := by
  classical
  obtain ⟨tA, htA, htAD, -, -, -, hLa2, hLsz, -⟩ := main_facts
  have htA' := htA
  rw [tA_eq] at htA'
  have ptTA : PtRep (PK 6) tA := ptRep_of_rep htA'
  have hγ : ∀ l, ∃ g ∈ twoBD, PtRep (sgS l) g := fun l => gens_ex _ (land15_lt l)
  choose γ hγD hγP using hγ
  have kinv : invK SG SGI 16 = true := by
    have k := kGen
    simp only [Bool.and_eq_true] at k
    exact k.2
  have hγI : ∀ l, PtRep (sgSI l) (γ l)⁻¹ := fun l => ptRep_inv (hγP l) fun i hi =>
    invK_spec kinv _ (land15_lt l) i hi
  let c : ℕ → Pm := treeE γ SP SL 5
  let z : ℕ → Pm := fun k => c k * tA * (c k)⁻¹
  have hcD : ∀ k, c k ∈ twoBD := treeE_mem hγD SP SL 5
  have hzD : ∀ k, z k ∈ twoBD := fun k => mul_mem (mul_mem (hcD k) htAD) (inv_mem (hcD k))
  have hzpt : ∀ k (x : Fin 1365), zK k x = (z k x : ℕ) := fun k x =>
    eK_eq hγP hγI ptTA SP SL 5 k x
  have hkey : ∀ k, keyS k = keyE (z k) := fun k => keyK_eq hγP hγI ptTA SP SL 5 k
  have hinj : ∀ i < 4095, ∀ j < 4095, z i = z j → i = j := fun i hi j hj h =>
    sortedK_injOn kKeys i hi j hj (by rw [hkey i, hkey j, h])
  have hle : {w : Pm | ∃ d ∈ twoBD, w = d * tA * d⁻¹}.ncard ≤ 4095 := by
    rw [← hLsz]
    exact ncard_le_of_rep fun w hw => hLa2 w hw
  have hcov := eq_image_of_ncard_le (Set.toFinite _) hle (f := z)
    (fun k _ => ⟨c k, hcD k, rfl⟩) hinj
  have kb := kBase
  simp only [Bool.and_eq_true] at kb
  obtain ⟨⟨kb0, -⟩, kb2⟩ := kb
  let b : ℕ → Pm := fun j => z (NB j)
  have hBB : ∀ j < 4, PtRep (BB j) (b j) := fun j hj x => by
    rw [ptEqK_spec (allN_spec kb2 j hj) x x.2]
    exact hzpt _ x
  have hb0 : b 0 = tA := by
    change z (NB 0) = tA
    rw [Nat.eq_of_beq_eq_true kb0]
    change treeE γ SP SL 5 0 * tA * (treeE γ SP SL 5 0)⁻¹ = tA
    rw [treeE_zero]
    simp
  have hbD : ∀ j, b j ∈ twoBD := fun j => hzD _
  have kw := kWords
  simp only [Bool.and_eq_true] at kw
  have hword : ∀ (W : ℕ → ℕ) (L S : ℕ) (u : Pm), PtRep S u → u ∈ twoBD →
      allN 3 (fun t => Nat.beq (wpB BB W L t) (ap S t)) = true → wordB b W L = u :=
    fun W L S u hS huD h => twoBD_eq_of_keyE (wordB_mem (fun j _ => hbD j) W L) huD
      (keyE_eq_of_pts fun x hx => by
        have h1 := Nat.eq_of_beq_eq_true (allN_spec h x hx)
        rw [wpB_eq hBB, hS] at h1
        exact Fin.ext h1)
  have hx := hword WX 847 _ xBar ptX hxD kw.1
  have hy := hword WY 24 _ yBar ptY hyD kw.2
  have hgen : Subgroup.closure (b '' {j | j < 4}) = twoBD := by
    have hmem : ∀ j < 4, b j ∈ Subgroup.closure (b '' {j | j < 4}) := fun j hj =>
      Subgroup.subset_closure ⟨j, hj, rfl⟩
    refine le_antisymm ((Subgroup.closure_le _).2 fun w ⟨j, _, hw⟩ => hw ▸ hbD j) ?_
    rw [← closure_gGen2 (1 : Pm), Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j < 2 := hj
    interval_cases j
    · have e : gGen 1 0 = xBar := by simp [gGen]
      rw [e, ← hx]
      exact wordB_mem hmem WX 847
    · have e : gGen 1 1 = yBar := by simp [gGen]
      rw [e, ← hy]
      exact wordB_mem hmem WY 24
  have hlet : ∀ (Z : ℕ → ℕ) (u : Pm), (∀ x : Fin 1365, Z x = (u x : ℕ)) → ∀ c, c ≤ 4 →
      ∀ x : Fin 1365, tlet Z BB c x = ((if c = 0 then u else b (c - 1)) x : ℕ) := by
    intro Z u hZ c hc x
    rw [tlet_eq]
    split_ifs with h0
    · exact hZ x
    · exact hBB (c - 1) (by omega) x
  have hmemg : ∀ (u : Pm), u ∈ twoBD → ∀ c, (if c = 0 then u else b (c - 1)) ∈ twoBD := by
    intro u hu c
    split_ifs
    · exact hu
    · exact hbD _
  have hrange := tst_range
  have hrefute : ∀ i, 1 ≤ i → i < 4 → ∀ k r, refK (fK k) (tst i) r = true →
      ∃ t ∈ tst i, orderOf (tupleWord b (z k) t.1) ≠ t.2 := by
    intro i h1 h4 k r h
    exact refK_spec (g := fun c => if c = 0 then z k else b (c - 1)) (H := twoBD)
      (fun t ht c hc => hlet (zK k) (z k) (hzpt k) c (by have := (hrange i h1 h4 t ht).1 c hc; omega))
      (fun t _ c _ => hmemg _ (hzD k) c) sepD h
  have hlev : ∀ i, 1 ≤ i → i < 4 → ∃ R SK : ℕ → ℕ, levK fK (tst i) R SK 4095 = true ∧
      cntK R SK 4095 ≤ (if i = 1 then 1024 else if i = 2 then 60 else 2) ∧
      ∀ k < 4095, SK k ≠ 0 → ∃ t ∈ tst i, orderOf (tupleWord b (z k) t.1) ≠ t.2 := by
    have kc := kCnt
    simp only [Bool.and_eq_true] at kc
    obtain ⟨⟨c1, c2⟩, c3⟩ := kc
    intro i h1 h4
    interval_cases i
    · exact ⟨_, _, kRef1, Nat.le_of_ble_eq_true c1, fun k _ h => absurd rfl h⟩
    · refine ⟨_, _, kRef2, Nat.le_of_ble_eq_true c2, fun k hk h => ?_⟩
      obtain ⟨t, ht, hne⟩ := hrefute 1 le_rfl (by norm_num) k _
        (levK_spec kRef1 k hk h rfl)
      exact ⟨t, tst_one_two t ht, hne⟩
    · exact ⟨_, _, kRef3, Nat.le_of_ble_eq_true c3, fun k _ h => absurd rfl h⟩
  have hown : ∀ i, 1 ≤ i → i < 4 → ownK (tlet (ap (BB i)) BB) (tst i) = true := by
    have ko := kOwn
    simp only [Bool.and_eq_true] at ko
    obtain ⟨⟨o1, o2⟩, o3⟩ := ko
    intro i h1 h4
    interval_cases i
    · exact o1
    · exact o2
    · exact o3
  refine ⟨b, tst, hb0 ▸ htA, fun j => ⟨c (NB j), hcD _, by rw [hb0]⟩, hgen,
    fun i h1 h4 => ⟨fun t ht => ⟨(hrange i h1 h4 t ht).1, (hrange i h1 h4 t ht).2, ?_⟩, ?_⟩⟩
  · exact ordK_spec (g := fun c => if c = 0 then b i else b (c - 1)) (H := twoBD)
      (fun c hc => hlet (ap (BB i)) (b i) (hBB i h4) c
        (by have := (hrange i h1 h4 t ht).1 c hc; omega))
      (fun c _ => hmemg _ (hbD i) c) sepD (hrange i h1 h4 t ht).2
      (ownK_spec (hown i h1 h4) t ht)
  · obtain ⟨R, SK, hl, hc, hsk⟩ := hlev i h1 h4
    refine le_trans ?_ (le_trans (le_of_eq (cntK_eq R SK 4095).symm) hc)
    refine ncard_le_countP' (f := z) _ fun w ⟨hwc, hwt⟩ => ?_
    rw [hb0] at hwc
    obtain ⟨k, hk, rfl⟩ := hcov w hwc
    refine ⟨k, hk, ?_, rfl⟩
    by_contra hp
    simp only [decide_eq_true_eq, not_and_or] at hp
    by_cases hs : SK k = 0
    · have hr : R k ≠ 0 := by
        rcases hp with h | h
        · exact h
        · exact absurd hs h
      obtain ⟨t, ht, hne⟩ := hrefute i h1 h4 k _ (levK_spec hl k hk hr hs)
      exact hne (hwt t ht)
    · obtain ⟨t, ht, hne⟩ := hsk k hk hs
      exact hne (hwt t ht)

theorem rigid_ok : ∃ b : ℕ → Equiv.Perm (Fin 1365), ∃ tests : ℕ → List (List ℕ × ℕ),
    Rep 1365 tAa (b 0) ∧
    (∀ j, ∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, b j = d * b 0 * d⁻¹) ∧
    Subgroup.closure (b '' {j | j < 4}) =
      Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya} ∧
    ∀ i, 1 ≤ i → i < 4 →
      (∀ t ∈ tests i, (∀ l ∈ t.1, l ≤ i) ∧ 0 < t.2 ∧ orderOf (tupleWord b (b i) t.1) = t.2) ∧
      {z | (∃ d ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya}, z = d * b 0 * d⁻¹) ∧
        ∀ t ∈ tests i, orderOf (tupleWord b z t.1) = t.2}.ncard ≤
        if i = 1 then 1024 else if i = 2 then 60 else 2 := by
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  rw [hX, hY]
  exact rigid_facts

end Main

end CertificateChecks.KernelG24.Rigid27205

end
