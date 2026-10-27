module

public import Certificates.Kernel.TwoM22.Gens
public import Certificates.Kernel.TwoM22.S0
public import Certificates.Kernel.TwoM22.S1
public import Certificates.Kernel.TwoM22.S2
public import Certificates.Kernel.TwoM22.S3
public import Certificates.Kernel.TwoM22.S4
public import Certificates.Kernel.TwoM22.S5
public import Certificates.Kernel.TwoM22.S6
public import Certificates.Kernel.TwoM22.S7
public import CFSG.Certificates.Kernel.TwoM22.Glue

public section

namespace CertificateChecks.TwoM22K

open CFSG.KC.Enum CFSG.KC.TwoM22 CFSG.KD.TwoM22 CFSG.KS CFSG.KS.Raw.Orb
  CFSG.Quasithin.TwoM22.Gens
open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native
  CFSG.LieType.Multipliers CFSG.Blueprint CFSG.Sporadic.Recognition.CoverRecipe
open CFSG.Sporadic.Mathieu (m22a m22b)

theorem prA : PRep 660 10 a a660P := prep_pkPerm perm_a
theorem prAi : PRep 660 10 ai a660P⁻¹ := prep_pkPerm_inv perm_a
theorem prB : PRep 660 10 b b660P := prep_pkPerm perm_b
theorem prBi : PRep 660 10 bi b660P⁻¹ := prep_pkPerm_inv perm_b
theorem prT : PRep 660 10 t t660P := prep_pkPerm perm_t

abbrev m22P (i : Fin 2) : Equiv.Perm (Fin 22) := (m22Gen i : NativeSporadic.M22)

theorem rep_m22Gen (i : Fin 2) :
    Rep 22 (wordTab 22 tabA tabA tabB tabBi (natWord (m22GenWords.getD i []))) (m22Gen i) := by
  have h1 := rep_wordTab (G := NativeSporadic.M22) (n := 22) (by norm_num)
    rep_a rep_a_inv rep_b rep_b_inv (natWord (m22GenWords.getD i []))
  have h2 : wordProd (img2 m22a m22b) (natWord (m22GenWords.getD i [])) = m22Gen i :=
    (lift_mk_eq_wordProd (img2 m22a m22b) (m22GenWords.getD i [])).symm.trans rfl
  rwa [h2] at h1

theorem tab_a22 : ∀ i < 22, pg 5 31 a22 i =
    ap (wordTab 22 tabA tabA tabB tabBi (natWord (m22GenWords.getD 0 []))) i := by
  decide +kernel

theorem tab_b22 : ∀ i < 22, pg 5 31 b22 i =
    ap (wordTab 22 tabA tabA tabB tabBi (natWord (m22GenWords.getD 1 []))) i := by
  decide +kernel

theorem prep_m22 {P : Nat} {i : Fin 2}
    (h : ∀ j < 22, pg 5 31 P j =
      ap (wordTab 22 tabA tabA tabB tabBi (natWord (m22GenWords.getD i []))) j) :
    PRep 22 5 P (m22P i) := by
  intro x
  change pg 5 31 P x = _
  rw [h x x.2, rep_m22Gen i x x.2, idx_of_lt _ x.2]
  rfl

theorem prA22 : PRep 22 5 a22 (m22P 0) := prep_m22 tab_a22
theorem prB22 : PRep 22 5 b22 (m22P 1) := prep_m22 tab_b22
theorem prA22i : PRep 22 5 ai22 (m22P 0)⁻¹ :=
  prep_inv prA22 fun i hi => ((permOK_facts perm_a22).2.2 i hi).2
theorem prB22i : PRep 22 5 bi22 (m22P 1)⁻¹ :=
  prep_inv prB22 fun i hi => ((permOK_facts perm_b22).2.2 i hi).2

theorem prT22 : PRep 22 5 t22 t22P := by
  intro x
  revert x
  decide +kernel

theorem prA' (x : Fin 660) : pg 10 1023 a x = a660P x := prA x
theorem prB' (x : Fin 660) : pg 10 1023 b x = b660P x := prB x
theorem prA22' (x : Fin 22) : pg 5 31 a22 x = m22P 0 x := prA22 x
theorem prB22' (x : Fin 22) : pg 5 31 b22 x = m22P 1 x := prB22 x

theorem snd_gen0 : (twoM22Gen 0).2 = m22P 0 := rfl
theorem snd_gen1 : (twoM22Gen 1).2 = m22P 1 := rfl

theorem pow22 (y : TwoM22W) : y ^ 22 = y ^ 11 * y ^ 11 := by
  rw [← pow_two, ← pow_mul]

theorem w660 (d : Nat × Nat) (x : Fin 660) :
    wpt 10 1023 a b ai bi d.1 d.2 x = ((wordOf twoM22Gen d).1 x : Nat) := by
  obtain ⟨W, len⟩ := d
  have e : (wordOf twoM22Gen (W, len)).1 = wordOf (fun i => (twoM22Gen i).1) (W, len) :=
    map_wordOf (MonoidHom.fst _ _) twoM22Gen (W, len)
  rw [e]
  exact wpt_eq (g := fun i => (twoM22Gen i).1) prA prB prAi prBi W len x

theorem w22 (d : Nat × Nat) (x : Fin 22) :
    wpt 5 31 a22 b22 ai22 bi22 d.1 d.2 x = ((wordOf twoM22Gen d).2 x : Nat) := by
  obtain ⟨W, len⟩ := d
  have e : (wordOf twoM22Gen (W, len)).2 = wordOf (fun i => (twoM22Gen i).2) (W, len) :=
    map_wordOf (MonoidHom.snd _ _) twoM22Gen (W, len)
  rw [e]
  exact wpt_eq (g := fun i => (twoM22Gen i).2) prA22 prB22 prA22i prB22i W len x

theorem wordOf_eq_one {d : Nat × Nat} (h1 : ∀ p < 660, wpt 10 1023 a b ai bi d.1 d.2 p = p)
    (h2 : ∀ p < 22, wpt 5 31 a22 b22 ai22 bi22 d.1 d.2 p = p) : wordOf twoM22Gen d = 1 := by
  refine Prod.ext (Equiv.ext fun x => Fin.ext ?_) (Equiv.ext fun x => Fin.ext ?_)
  · rw [Prod.fst_one, Equiv.Perm.one_apply, ← w660]
    exact h1 x x.2
  · rw [Prod.snd_one, Equiv.Perm.one_apply, ← w22]
    exact h2 x x.2

@[expose] def code (l : Fin 2 × Bool) : Nat := if l.2 then l.1.val else l.1.val + 2

theorem letterOf_code {G : Type*} [Group G] (g : Fin 2 → G) (l : Fin 2 × Bool) :
    letterOf g (code l) = cond l.2 (g l.1) (g l.1)⁻¹ := by
  obtain ⟨i, s⟩ := l
  fin_cases i <;> cases s <;> simp [letterOf, code]

theorem lift_eq_wordOf {G : Type*} [Group G] (g : Fin 2 → G) (r : List (Fin 2 × Bool))
    (d : Nat × Nat) (h : wordCodes d = r.map code) :
    FreeGroup.lift g (FreeGroup.mk r) = wordOf g d := by
  rw [wordOf_eq, h, List.map_map, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro l _
  exact (letterOf_code g l).symm

theorem cover_codes : m22Cover.map (fun r => r.map code) = cover.map wordCodes := by
  decide +kernel

theorem twoM22_rel : ∀ r ∈ m22Cover, FreeGroup.lift twoM22Gen (FreeGroup.mk r) = 1 := by
  intro r hr
  have hm : r.map code ∈ cover.map wordCodes := by
    rw [← cover_codes]
    exact List.mem_map.2 ⟨r, hr, rfl⟩
  obtain ⟨d, hd, hcd⟩ := List.mem_map.1 hm
  rw [lift_eq_wordOf twoM22Gen r d hcd]
  exact wordOf_eq_one (relOK_sound rel660 d hd) (relOK_sound rel22 d hd)

theorem codes_z11 : wordCodes z11 = List.replicate 11 1 := by decide +kernel

theorem codes_z22 : wordCodes z22 = List.replicate 22 1 := by decide +kernel

theorem wordOf_replicate {G : Type*} [Group G] (g : Fin 2 → G) {d : Nat × Nat} {k : Nat}
    (h : wordCodes d = List.replicate k 1) : wordOf g d = g 1 ^ k := by
  rw [wordOf_eq, h, List.map_replicate, List.prod_replicate]
  simp [letterOf]

theorem zeta_eq : wordOf twoM22Gen z11 = twoM22Gen 1 ^ 11 := wordOf_replicate _ codes_z11

theorem zeta_fst_zero : ((twoM22Gen 1 ^ 11).1 ⟨0, by norm_num⟩ : Nat) = 635 := by
  have h := Nat.eq_of_beq_eq_true zeta_zero
  have h2 := w660 z11 ⟨0, by norm_num⟩
  rw [zeta_eq] at h2
  exact h2.symm.trans h

theorem zeta_fst_635 : ((twoM22Gen 1 ^ 11).1 ⟨635, by norm_num⟩ : Nat) = 0 := by
  have h := Nat.eq_of_beq_eq_true zeta_635
  have h2 := w660 z11 ⟨635, by norm_num⟩
  rw [zeta_eq] at h2
  exact h2.symm.trans h

theorem zeta_snd : (twoM22Gen 1 ^ 11).2 = 1 := by
  rw [← zeta_eq]
  refine Equiv.ext fun x => Fin.ext ?_
  rw [Equiv.Perm.one_apply, ← w22]
  exact wordId_sound zeta22 x x.2

theorem twoM22_zeta_ne_one : twoM22Gen 1 ^ 11 ≠ 1 := by
  intro h
  have h0 := zeta_fst_zero
  rw [h] at h0
  simp at h0

theorem twoM22_zeta_sq : twoM22Gen 1 ^ 22 = 1 := by
  refine Prod.ext ?_ ?_
  · rw [← wordOf_replicate twoM22Gen codes_z22]
    refine Equiv.ext fun x => Fin.ext ?_
    rw [Prod.fst_one, Equiv.Perm.one_apply, ← w660]
    exact wordId_sound zeta_sq x x.2
  · rw [pow22, Prod.snd_mul, zeta_snd, mul_one, Prod.snd_one]

theorem twoM22T_mul_self : twoM22T * twoM22T = 1 := by
  refine Prod.ext ?_ ?_
  · change t660P * t660P = 1
    refine Equiv.ext fun x => Fin.ext ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, ← prT, ← prT]
    exact ((permOK_facts perm_t).2.2 x x.2).2
  · change t22P * t22P = 1
    refine Equiv.ext fun x => ?_
    revert x
    decide +kernel

theorem twoM22T_inv : twoM22T⁻¹ = twoM22T := inv_eq_of_mul_eq_one_right twoM22T_mul_self

theorem conj_fst {x : Equiv.Perm (Fin 660)} {X : Nat} (hX : PRep 660 10 X x) {d : Nat × Nat}
    (h : ∀ p < 660, pg 10 1023 t (pg 10 1023 X (pg 10 1023 t p)) =
      wpt 10 1023 a b ai bi d.1 d.2 p) :
    t660P * x * t660P = (wordOf twoM22Gen d).1 := by
  refine Equiv.ext fun y => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← prT, ← hX, ← prT, ← w660]
  exact h y y.2

theorem conj_snd {x : Equiv.Perm (Fin 22)} {X : Nat} (hX : PRep 22 5 X x) {d : Nat × Nat}
    (h : ∀ p < 22, pg 5 31 t22 (pg 5 31 X (pg 5 31 t22 p)) =
      wpt 5 31 a22 b22 ai22 bi22 d.1 d.2 p) :
    t22P * x * t22P = (wordOf twoM22Gen d).2 := by
  refine Equiv.ext fun y => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← prT22, ← hX, ← prT22, ← w22]
  exact h y y.2

theorem conj_zero : twoM22T * twoM22Gen 0 * twoM22T = wordOf twoM22Gen wa :=
  Prod.ext (conj_fst prA (conjOK_sound conj_a)) (conj_snd prA22 (conjOK_sound conj_a22))

theorem conj_one : twoM22T * twoM22Gen 1 * twoM22T = wordOf twoM22Gen wb :=
  Prod.ext (conj_fst prB (conjOK_sound conj_b)) (conj_snd prB22 (conjOK_sound conj_b22))

theorem twoM22T_conj_mem (i : Fin 2) :
    twoM22T * twoM22Gen i * twoM22T⁻¹ ∈ twoM22M := by
  rw [twoM22T_inv]
  fin_cases i
  · exact conj_zero ▸ wordOf_mem _ _
  · exact conj_one ▸ wordOf_mem _ _

theorem T_conj_M {m : TwoM22W} (hm : m ∈ twoM22M) : twoM22T * m * twoM22T ∈ twoM22M := by
  induction hm using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    have := twoM22T_conj_mem i
    rwa [twoM22T_inv] at this
  | one => rw [mul_one, twoM22T_mul_self]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : twoM22T * (x * y) * twoM22T = (twoM22T * x * twoM22T) * (twoM22T * y * twoM22T) := by
      simp only [mul_assoc]
      rw [← mul_assoc twoM22T twoM22T, twoM22T_mul_self, one_mul]
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : twoM22T * x⁻¹ * twoM22T = (twoM22T * x * twoM22T)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, twoM22T_inv, mul_assoc]
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem sign_m22gA : Equiv.Perm.sign CFSG.Sporadic.Mathieu.m22gA = 1 := by decide

theorem sign_m22gB : Equiv.Perm.sign CFSG.Sporadic.Mathieu.m22gB = 1 := by
  rw [CFSG.Sporadic.Mathieu.m22gB, map_mul, map_mul, map_mul, map_mul, map_mul]
  decide

theorem sign_m22 (g : NativeSporadic.M22) :
    Equiv.Perm.sign ((g : NativeSporadic.M22) : Equiv.Perm (Fin 22)) = 1 := by
  have h : NativeSporadic.M22 ≤ (Equiv.Perm.sign : Equiv.Perm (Fin 22) →* ℤˣ).ker := by
    rw [CFSG.Sporadic.Mathieu.m22_eq, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact MonoidHom.mem_ker.mpr sign_m22gA
    · exact MonoidHom.mem_ker.mpr sign_m22gB
  exact MonoidHom.mem_ker.mp (h g.2)

theorem sign_t22P : Equiv.Perm.sign t22P = -1 := by decide

theorem twoM22T_not_mem : twoM22T ∉ twoM22M := by
  intro hT
  have hle : twoM22M ≤ (Equiv.Perm.sign.comp (MonoidHom.snd (Equiv.Perm (Fin 660))
      (Equiv.Perm (Fin 22)))).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨i, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    fin_cases i
    · exact sign_m22 (m22Gen 0)
    · exact sign_m22 (m22Gen 1)
  have h := MonoidHom.mem_ker.mp (hle hT)
  rw [MonoidHom.comp_apply] at h
  change Equiv.Perm.sign t22P = 1 at h
  rw [sign_t22P] at h
  exact absurd h (by decide)

theorem lift_m22B11_zeta : FreeGroup.lift twoM22Gen (FreeGroup.mk m22B11) =
    twoM22Gen 1 ^ 11 := by
  rw [m22B11, m22Word, List.map_replicate]
  have hab : abLetter 2 = (⟨1, by decide⟩, true) := rfl
  rw [hab, FreeGroup.lift_mk]
  change (List.map (fun l : Fin 2 × Bool =>
      if l.2 then twoM22Gen l.1 else (twoM22Gen l.1)⁻¹)
      (List.replicate 11 (⟨1, by decide⟩, true))).prod = twoM22Gen 1 ^ 11
  have hmap : (List.map (fun l : Fin 2 × Bool =>
      if l.2 then twoM22Gen l.1 else (twoM22Gen l.1)⁻¹)
      (List.replicate 11 (⟨1, by decide⟩, true))) = List.replicate 11 (twoM22Gen 1) := by
    rw [List.map_replicate]
    rfl
  rw [hmap, List.prod_replicate]

theorem commWord_b11_mem (i : Fin 2) : commWord [(i, true)] m22B11 ∈ m22Cover := by
  unfold m22Cover coverWords
  exact List.mem_append_left _ (List.mem_flatMap.mpr
    ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨m22B11, m22B11_mem, rfl⟩⟩)

theorem zeta_gen_comm (i : Fin 2) :
    twoM22Gen 1 ^ 11 * twoM22Gen i = twoM22Gen i * twoM22Gen 1 ^ 11 := by
  have h := twoM22_rel _ (commWord_b11_mem i)
  rw [mk_commWord, map_commutatorElement, lift_m22B11_zeta] at h
  exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm

theorem twoM22_cent (x : TwoM22W) (hx : ∀ m ∈ twoM22M, x * m = m * x) :
    x = 1 ∨ x = twoM22Gen 1 ^ 11 := by
  have hg : ∀ i, twoM22Gen i ∈ twoM22M := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have c1 : ∀ m ∈ twoM22M, x.1 * m.1 = m.1 * x.1 := fun m hm => congrArg Prod.fst (hx m hm)
  have c2 : ∀ m ∈ twoM22M, x.2 * m.2 = m.2 * x.2 := fun m hm => congrArg Prod.snd (hx m hm)
  have hx2 : x.2 = 1 := by
    have hfix := fix1OK_sound fix22
    have h0 : x.2 0 = 0 := by
      apply Fin.ext
      refine (hfix _ (x.2 0).2).1 fun d hd => ?_
      have hd0 : (wordOf twoM22Gen d).2 0 = 0 := Fin.ext (by
        rw [← w22]
        exact (hfix 0 (by norm_num)).2 rfl d hd)
      rw [w22, ← perm_comm_apply (c2 _ (wordOf_mem twoM22Gen d)), hd0]
    have hc0 := c2 _ (hg 0)
    have hc1 := c2 _ (hg 1)
    rw [snd_gen0] at hc0
    rw [snd_gen1] at hc1
    exact eq_one_of_tree (by norm_num) prA22' prB22' tree22 hc0 hc1 h0
  have hfix := fix2OK_sound fix660
  have hh0 : (wordOf twoM22Gen h660).1 0 = 0 := Fin.ext (by
    rw [← w660]
    exact (hfix 0 (by norm_num)).2 (Or.inl rfl))
  have hx1 : (x.1 0 : Nat) = 0 ∨ (x.1 0 : Nat) = 635 := by
    refine (hfix _ (x.1 0).2).1 ?_
    rw [w660, ← perm_comm_apply (c1 _ (wordOf_mem twoM22Gen h660)), hh0]
  rcases hx1 with h0 | h0
  · left
    refine Prod.ext ?_ hx2
    exact eq_one_of_tree (by norm_num) prA' prB' tree660 (c1 _ (hg 0)) (c1 _ (hg 1)) (Fin.ext h0)
  · right
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = twoM22Gen 1 ^ 11 := ⟨_, rfl⟩
    have hZc : ∀ i, Z.1 * (twoM22Gen i).1 = (twoM22Gen i).1 * Z.1 := fun i => by
      rw [hZ]
      exact congrArg Prod.fst (zeta_gen_comm i)
    have hxc : ∀ i, x.1 * (twoM22Gen i).1 = (twoM22Gen i).1 * x.1 := fun i => c1 _ (hg i)
    have hyc : ∀ i, (x.1 * Z.1) * (twoM22Gen i).1 = (twoM22Gen i).1 * (x.1 * Z.1) := by
      intro i
      rw [mul_assoc, hZc i, ← mul_assoc, hxc i, mul_assoc]
    have hZ635 : Z.1 ⟨635, by norm_num⟩ = 0 := Fin.ext (by rw [hZ]; exact zeta_fst_635)
    have hx0 : x.1 0 = ⟨635, by norm_num⟩ := Fin.ext h0
    have hZM : Z ∈ twoM22M := by
      rw [hZ]
      exact Subgroup.pow_mem _ (hg 1) 11
    have hxz : x.1 * Z.1 = Z.1 * x.1 := congrArg Prod.fst (hx Z hZM)
    have hy0 : (x.1 * Z.1) 0 = 0 := by
      rw [Equiv.Perm.mul_apply, perm_comm_apply hxz, hx0, hZ635]
    have hy : x.1 * Z.1 = 1 :=
      eq_one_of_tree (by norm_num) prA' prB' tree660 (hyc 0) (hyc 1) hy0
    have hZsq : Z.1 * Z.1 = 1 := by
      have h := twoM22_zeta_sq
      rw [pow22, ← hZ] at h
      exact congrArg Prod.fst h
    rw [← hZ]
    refine Prod.ext ?_ ?_
    · calc x.1 = x.1 * (Z.1 * Z.1) := by rw [hZsq, mul_one]
        _ = (x.1 * Z.1) * Z.1 := by rw [mul_assoc]
        _ = Z.1 := by rw [hy, one_mul]
    · rw [hx2, hZ, zeta_snd]

noncomputable def sgenN (g : Nat) : TwoM22W :=
  if h : g < 4 then twoM22SGen ⟨g, h⟩ else twoM22T0

theorem sgenN_mem_S {g : Nat} (hg : g < 5) : sgenN g ∈ twoM22S := by
  unfold sgenN
  split_ifs with h
  · exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr rfl)

theorem sgen_rep (g : Nat) (hg : g < 5) :
    (∀ x : Fin 660, pg 10 1023 (g660.getD g 0) x = (sgenN g).1 x) ∧
      (∀ x : Fin 22, pg 5 31 (g22.getD g 0) x = (sgenN g).2 x) := by
  by_cases h4 : g < 4
  · have e : sgenN g = wordOf twoM22Gen (sw.getD g (0, 0)) := by
      rw [sgenN, dif_pos h4]
      rfl
    rw [e]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [← w660]
      exact wordEqOK_sound (allN_iff.1 sgen660 g h4) x x.2
    · rw [← w22]
      exact wordEqOK_sound (allN_iff.1 sgen22 g h4) x x.2
  · obtain rfl : g = 4 := by omega
    have e : sgenN 4 = wordOf twoM22Gen t0w * twoM22T := by
      rw [sgenN, dif_neg (by omega)]
      rfl
    rw [e]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [Prod.fst_mul, Equiv.Perm.mul_apply, ← w660]
      have ht : ((twoM22T.1 x : Fin 660) : Nat) = pg 10 (mask 10) t x := (prT x).symm
      rw [ht]
      exact wordMulOK_sound t0_660 x x.2
    · rw [Prod.snd_mul, Equiv.Perm.mul_apply, ← w22]
      have ht : ((twoM22T.2 x : Fin 22) : Nat) = pg 5 (mask 5) t22 x := (prT22 x).symm
      rw [ht]
      exact wordMulOK_sound t0_22 x x.2

theorem recs_all : ∀ k < 512, recOK RT g660 g22 a b ai bi z11.1 z11.2 k = true := by
  refine recRange_sound fun c hc => ?_
  interval_cases c
  exacts [recs0, recs1, recs2, recs3, recs4, recs5, recs6, recs7]

@[expose] def RepS (k : Nat) (y : TwoM22W) : Prop :=
  (∀ x : Fin 660, pg 10 1023 (rE RT k) x = y.1 x) ∧ (∀ x : Fin 22, pg 5 31 (rE22 RT k) x = y.2 x)

theorem repS_unique {k : Nat} {y z : TwoM22W} (hy : RepS k y) (hz : RepS k z) : y = z :=
  Prod.ext (Equiv.ext fun x => Fin.ext ((hy.1 x).symm.trans (hz.1 x)))
    (Equiv.ext fun x => Fin.ext ((hy.2 x).symm.trans (hz.2 x)))

theorem repS_ne {k l : Nat} {y z : TwoM22W} (hk : k < 512) (hl : l < 512) (hkl : k ≠ l)
    (hy : RepS k y) (hz : RepS l z) : y ≠ z := by
  rintro rfl
  obtain ⟨i, hi, hne⟩ := (recOK_sound recs_all).1 k hk l hl hkl
  exact hne ((hy.1 ⟨i, hi⟩).trans (hz.1 ⟨i, hi⟩).symm)

theorem repS_mul {k g : Nat} {y : TwoM22W} (hk : k < 512) (hg : g < 5) (h : RepS k y) :
    RepS (rR RT k g) (y * sgenN g) := by
  obtain ⟨-, h660, h22⟩ := (recOK_sound recs_all).2.1 k hk g hg
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [h660 x x.2, (sgen_rep g hg).1 x, h.1, Prod.fst_mul, Equiv.Perm.mul_apply]
  · rw [h22 x x.2, (sgen_rep g hg).2 x, h.2, Prod.snd_mul, Equiv.Perm.mul_apply]

theorem sId_facts : sId < 512 ∧ rDep RT sId = 0 := by
  obtain ⟨h1, h2⟩ := bAnd_true (a := Nat.blt sId 512) (b := Nat.beq (rDep RT sId) 0) sId_ok
  rw [Nat.blt_eq] at h1
  exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩

theorem repS_one : RepS sId 1 := by
  obtain ⟨h1, h2, -⟩ := (recOK_sound recs_all).2.2.1 sId sId_facts.1 sId_facts.2
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [Prod.fst_one, Equiv.Perm.one_apply]
    exact h1 x x.2
  · rw [Prod.snd_one, Equiv.Perm.one_apply]
    exact h2 x x.2

theorem repS_of_mem {y : TwoM22W} (hy : y ∈ twoM22S) : ∃ k < 512, RepS k y := by
  let P : TwoM22W → Prop := fun y => ∃ k < 512, RepS k y
  have hgen : ∀ g < 5, ∀ z, P z → P (z * sgenN g) := fun g hg z ⟨k, hk, h⟩ =>
    ⟨rR RT k g, ((recOK_sound recs_all).2.1 k hk g hg).1, repS_mul hk hg h⟩
  have hQ : ∀ z, P z → P (z * y) := by
    induction hy using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨g, hg, rfl⟩ : ∃ g < 5, sgenN g = s := by
        rcases hs with ⟨j, rfl⟩ | hs
        · refine ⟨j.val, by omega, ?_⟩
          rw [sgenN, dif_pos j.2]
        · refine ⟨4, by norm_num, ?_⟩
          rw [Set.mem_singleton_iff.1 hs, sgenN, dif_neg (by omega)]
      exact hgen g hg
    | one =>
      intro z hz
      rwa [mul_one]
    | mul a b _ _ iha ihb =>
      intro z hz
      rw [← mul_assoc]
      exact ihb _ (iha z hz)
    | inv a _ iha =>
      intro z hz
      have hpa : ∀ j : Nat, ∀ z, P z → P (z * a ^ j) := by
        intro j
        induction j with
        | zero =>
          intro z hz
          rwa [pow_zero, mul_one]
        | succ j ih =>
          intro z hz
          rw [pow_succ, ← mul_assoc]
          exact iha _ (ih z hz)
      have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [pow_sub_one_mul (orderOf_pos a).ne', pow_orderOf_eq_one]
      rw [hinv]
      exact hpa _ z hz
  have h := hQ 1 ⟨sId, sId_facts.1, repS_one⟩
  rwa [one_mul] at h

theorem rOdd_le (k : Nat) : rOdd RT k ≤ 1 := Nat.and_le_right

theorem good : ∀ d, ∀ k < 512, rDep RT k = d → ∃ y ∈ twoM22S, RepS k y ∧
    (rOdd RT k = 0 → y ∈ twoM22M) ∧ (rOdd RT k ≠ 0 → y * twoM22T ∈ twoM22M) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hk hd
    by_cases hd0 : rDep RT k = 0
    · obtain ⟨h1, h2, h3⟩ := (recOK_sound recs_all).2.2.1 k hk hd0
      refine ⟨1, Subgroup.one_mem _, ⟨fun x => ?_, fun x => ?_⟩, fun _ => Subgroup.one_mem _,
        fun h => absurd h3 h⟩
      · rw [Prod.fst_one, Equiv.Perm.one_apply]
        exact h1 x x.2
      · rw [Prod.snd_one, Equiv.Perm.one_apply]
        exact h2 x x.2
    obtain ⟨hpar, hlab, hdep, hR, hodd⟩ := (recOK_sound recs_all).2.2.2.1 k hk hd0
    obtain ⟨y, hyS, hy, hyM, hyT⟩ := ih _ (by omega) _ hpar rfl
    have hrep := repS_mul hpar hlab hy
    rw [hR] at hrep
    refine ⟨y * sgenN (rLab RT k), Subgroup.mul_mem _ hyS (sgenN_mem_S hlab), hrep, ?_⟩
    have hTT := twoM22T_mul_self
    have split : ∀ p s : TwoM22W, p * s * twoM22T = (p * twoM22T) * (twoM22T * s * twoM22T) := by
      intro p s
      simp only [mul_assoc]
      rw [← mul_assoc twoM22T twoM22T, hTT, one_mul]
    have hop := rOdd_le (rPar RT k)
    by_cases hl : rLab RT k = 4
    · have hs : sgenN (rLab RT k) = wordOf twoM22Gen t0w * twoM22T := by
        rw [hl, sgenN, dif_neg (by omega)]
        rfl
      have hu := wordOf_mem twoM22Gen t0w
      rw [if_pos hl] at hodd
      rw [hs]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hop with h0 | h0
      · rw [h0] at hodd
        have hp := hyM h0
        refine ⟨fun h => absurd (h.symm.trans hodd) (by decide), fun _ => ?_⟩
        have e : y * (wordOf twoM22Gen t0w * twoM22T) * twoM22T = y * wordOf twoM22Gen t0w := by
          simp only [mul_assoc]
          rw [hTT, mul_one]
        rw [e]
        exact Subgroup.mul_mem _ hp hu
      · rw [h0] at hodd
        have hp := hyT (by omega)
        refine ⟨fun _ => ?_, fun h => absurd (hodd.trans (by decide)) h⟩
        have e : y * (wordOf twoM22Gen t0w * twoM22T) =
            (y * twoM22T) * (twoM22T * wordOf twoM22Gen t0w * twoM22T) := by
          simp only [mul_assoc]
          rw [← mul_assoc twoM22T twoM22T, hTT, one_mul]
        rw [e]
        exact Subgroup.mul_mem _ hp (T_conj_M hu)
    · have hs : sgenN (rLab RT k) ∈ twoM22M := by
        rw [sgenN, dif_pos (by omega)]
        exact wordOf_mem _ _
      rw [if_neg hl, Nat.xor_zero] at hodd
      rw [hodd]
      refine ⟨fun h => Subgroup.mul_mem _ (hyM h) hs, fun h => ?_⟩
      rw [split]
      exact Subgroup.mul_mem _ (hyT h) (T_conj_M hs)

theorem twoM22S_le : twoM22S ≤ twoM22M ⊔ Subgroup.zpowers twoM22T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro s (⟨j, rfl⟩ | hs)
  · exact Subgroup.mem_sup_left (wordOf_mem twoM22Gen _)
  · rw [Set.mem_singleton_iff.1 hs]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (wordOf_mem twoM22Gen _))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem card_twoM22S : Nat.card twoM22S = 2 ^ 9 := by
  have hex : ∀ k : Fin 512, ∃ y : twoM22S, RepS k y := fun k => by
    obtain ⟨y, hy, hr, -⟩ := good _ k k.2 rfl
    exact ⟨⟨y, hy⟩, hr⟩
  choose f hf using hex
  have hbij : Function.Bijective f := by
    constructor
    · intro k l hkl
      by_contra hne
      exact repS_ne k.2 l.2 (fun h => hne (Fin.ext h)) (hf k) (hf l) (congrArg Subtype.val hkl)
    · intro y
      obtain ⟨k, hk, hr⟩ := repS_of_mem y.2
      exact ⟨⟨k, hk⟩, Subtype.ext (repS_unique (hf ⟨k, hk⟩) hr)⟩
  have h := Nat.card_eq_of_bijective f hbij
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h.symm.trans (by norm_num)

theorem twoM22S_sq_ne : ∀ y ∈ twoM22S, y ∉ twoM22M → y * y ≠ twoM22Gen 1 ^ 11 := by
  intro y hy hyM hsq
  obtain ⟨k, hk, hrep⟩ := repS_of_mem hy
  obtain ⟨y', -, hrep', hev, -⟩ := good _ k hk rfl
  have e := repS_unique hrep' hrep
  by_cases h0 : rOdd RT k = 0
  · exact hyM (e ▸ hev h0)
  obtain ⟨hx, hne⟩ := (recOK_sound recs_all).2.2.2.2 k hk h0
  apply hne
  have e1 : pg 10 1023 (rE RT k) (rPt RT k) = (y.1 ⟨rPt RT k, hx⟩ : Nat) := hrep.1 ⟨_, hx⟩
  have e2 := hrep.1 (y.1 ⟨rPt RT k, hx⟩)
  have e3 : wpt 10 1023 a b ai bi z11.1 z11.2 (rPt RT k) = ((y * y).1 ⟨rPt RT k, hx⟩ : Nat) := by
    have h := w660 z11 ⟨rPt RT k, hx⟩
    rw [zeta_eq, ← hsq] at h
    exact h
  rw [e1, e2, e3, Prod.fst_mul, Equiv.Perm.mul_apply]

theorem facts :
    (∀ r ∈ m22Cover, FreeGroup.lift twoM22Gen (FreeGroup.mk r) = 1) ∧
    twoM22Gen 1 ^ 11 ≠ 1 ∧ twoM22Gen 1 ^ 22 = 1 ∧ twoM22T * twoM22T = 1 ∧
    (∀ i, twoM22T * twoM22Gen i * twoM22T⁻¹ ∈ twoM22M) ∧ twoM22T ∉ twoM22M ∧
    (∀ x : TwoM22W, (∀ m ∈ twoM22M, x * m = m * x) → x = 1 ∨ x = twoM22Gen 1 ^ 11) ∧
    twoM22S ≤ twoM22M ⊔ Subgroup.zpowers twoM22T ∧ Nat.card twoM22S = 2 ^ 9 ∧
    (∀ y ∈ twoM22S, y ∉ twoM22M → y * y ≠ twoM22Gen 1 ^ 11) :=
  ⟨twoM22_rel, twoM22_zeta_ne_one, twoM22_zeta_sq, twoM22T_mul_self, twoM22T_conj_mem,
    twoM22T_not_mem, twoM22_cent, twoM22S_le, card_twoM22S, twoM22S_sq_ne⟩

end CertificateChecks.TwoM22K

end
