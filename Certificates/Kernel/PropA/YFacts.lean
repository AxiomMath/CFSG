module

public import Certificates.Kernel.PropA.G5Facts
public import Certificates.Kernel.PropA.KFacts
public import Certificates.Kernel.PropA.YChk

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw.Orb
  CFSG.KS.PRec CFSG.KS.PMem CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA

theorem pa450010_clXR : pa450010cl false 2 pa450010wXR = zpowers pa450010x := by
  rw [zpowers_eq_closure]
  unfold pa450010cl
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj0 : j = 0 := by
      have h1 : j < 1 := hj
      omega
    subst hj0
    exact pa450010wv_wx false le_rfl
  · rintro rfl
    exact ⟨0, by decide, pa450010wv_wx false le_rfl⟩

theorem pa450010_XR_rec : ∃ x : ℕ → Perm (Fin 28),
    (∀ i < pa450010XR.cnt, PRep 28 5 (pa450010XR.T i) (x i)) ∧
    (∀ y, y ∈ zpowers pa450010x ↔ ∃ i < pa450010XR.cnt, x i = y) := by
  obtain ⟨x, hx, -, hmem, -, -, -, -⟩ := pa450010_rec (b := false) (by norm_num)
    pa450010_XR_hd pa450010_XR_sl
  rw [pa450010_clXR] at hmem
  exact ⟨x, hx, hmem⟩

theorem pa450010_x_order : orderOf pa450010x = 2 := by
  obtain ⟨x, hx, -, hmem, hcard, -, -, -⟩ := pa450010_rec (b := false) (by norm_num)
    pa450010_XR_hd pa450010_XR_sl
  rw [pa450010_clXR, Nat.card_zpowers] at hcard
  exact hcard

theorem pa450010_zpowers_x {g : Perm (Fin 28)} (h : g ∈ zpowers pa450010x) :
    g = 1 ∨ g = pa450010x := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 h
  have e2 : ((orderOf pa450010x : ℕ) : ℤ) = 2 := by
    rw [pa450010_x_order]
    rfl
  rw [← zpow_mod_orderOf, e2]
  rcases Int.emod_two_eq_zero_or_one n with e | e
  · left
    rw [e, zpow_zero]
  · right
    rw [e, zpow_one]

@[expose] noncomputable def pa450010u : Perm (Fin 28) := pa450010wv false 2 pa450010wu

theorem pa450010_prepU : PRep 28 5 pa450010UD.R pa450010u :=
  pa450010_root (b := false) (kS := 2) (by norm_num) pa450010_UD_root

theorem pa450010_u_mem_J : pa450010u ∈ pa450010Jg := by
  obtain ⟨xJ, hxJ, -, hmem, -, -, -, -⟩ := pa450010_J_rec
  exact mem_of_atK hxJ hmem pa450010_prepU pa450010_U_inJ

theorem pa450010_card_Du :
    Nat.card ↥(D28 ⊓ centralizer ({pa450010u} : Set (Perm (Fin 28)))) = 36 := by
  obtain ⟨hh, hN, hk, hg, hgi⟩ := recHdK_gens (by norm_num) (by norm_num)
    (pa450010_prepSk false (kS := 2) (by norm_num)) (pa450010_prepSIk false (by norm_num))
    pa450010_UD_hd
  have hp : ∀ i < pa450010UD.cnt, penumPtK 28 5 (mask 5) (28 * 5) true pa450010UD.G
      pa450010UD.GI pa450010UD.k pa450010UD.cnt pa450010UD.T pa450010UD.PL pa450010UD.POS
      pa450010UD.SRT pa450010UD.SRI i = true := by
    intro i hi
    by_cases h1 : i < 1000
    · exact penumSlK_pt pa450010_UD_sl0 (Nat.zero_le i) (by omega) hi
    · by_cases h2 : i < 2000
      · exact penumSlK_pt pa450010_UD_sl1 (by omega) (by omega) hi
      · exact penumSlK_pt pa450010_UD_sl2 (by omega) (by omega) hi
  obtain ⟨c, -, hinj, hcls⟩ := penumConj_class (by norm_num) (by norm_num) hg hgi pa450010_prepU
    hh hp
  have hcls' : ∀ y, (∃ h ∈ closure ((fun j => pa450010wv false 2 pa450010wD[j]!) ''
      {j | j < pa450010wD.length}), h * pa450010u * h⁻¹ = y) ↔ ∃ i < pa450010UD.cnt, c i = y :=
    fun y => by
      rw [← hcls y, hk]
      exact Iff.rfl
  rw [pa450010_clD] at hcls'
  have h := pa450010_size (pa450010wv_memD false _) hcls' hinj
  have h2 : 2640 * Nat.card ↥(D28 ⊓ centralizer ({pa450010u} : Set (Perm (Fin 28)))) = 95040 := by
    rw [← hN, ← card_D28]
    exact h
  omega

theorem pa450010_Du_eq :
    D28 ⊓ centralizer ({pa450010u} : Set (Perm (Fin 28))) = pa450010cl false 2 pa450010wCDU := by
  obtain ⟨-, -, -, -, hcard, hk, hg, -⟩ := pa450010_rec (b := false) (by norm_num) pa450010_CDU_hd
    pa450010_CDU_sl
  have hc := closure_le_centralizer (by norm_num) hg pa450010_prepU pa450010_CDU_cent
  rw [hk] at hc
  have hle : pa450010cl false 2 pa450010wCDU ≤
      D28 ⊓ centralizer ({pa450010u} : Set (Perm (Fin 28))) :=
    le_inf ((closure_le _).2 (by rintro _ ⟨j, -, rfl⟩; exact pa450010wv_memD false _)) hc
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [pa450010_card_Du, hcard])).symm

theorem pa450010_x_mem_CJ : pa450010x ∈ centralizer (pa450010Jg : Set (Perm (Fin 28))) :=
  mem_centralizer_iff.2 fun _ hh => mem_centralizer_singleton_iff.1 (pa450010_J_le_E hh).2

theorem pa450010_CDJ :
    D28 ⊓ centralizer (pa450010Jg : Set (Perm (Fin 28))) = zpowers pa450010x := by
  apply le_antisymm
  · rintro g ⟨hgD, hgJ⟩
    obtain ⟨xJ, -, -, -, -, -, hgJg, -⟩ := pa450010_J_rec
    obtain ⟨xU, hxU, -, hmemU, -, -, -, -⟩ := pa450010_rec (b := false) (by norm_num)
      pa450010_CDU_hd pa450010_CDU_sl
    obtain ⟨xX, hxX, hmemX⟩ := pa450010_XR_rec
    have hgu : g ∈ D28 ⊓ centralizer ({pa450010u} : Set (Perm (Fin 28))) :=
      ⟨hgD, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hgJ _ pa450010_u_mem_J).symm⟩
    rw [pa450010_Du_eq] at hgu
    obtain ⟨q, hq, rfl⟩ := (hmemU _).1 hgu
    obtain ⟨q', hq', e⟩ := filtInK_spec (by norm_num) (by norm_num) hxU hxX hgJg pa450010_CDU_filt
      q hq fun j hj => (mem_centralizer_iff.1 hgJ _ (pa450010_j_mem hj)).symm
    exact (hmemX _).2 ⟨q', hq', e⟩
  · rw [zpowers_le]
    exact ⟨pa450010_x_memD, pa450010_x_mem_CJ⟩

theorem pa450010_pT_mem (b : Bool) : pT ∈ K28 b := by
  have e : pa450010gK b 3 = pT := by simp [pa450010gK]
  rw [← e]
  exact pa450010gK_mem b 3

theorem pa450010_clTX (b : Bool) :
    pa450010cl b 4 pa450010wTX = closure ({pT, pa450010x} : Set (Perm (Fin 28))) := by
  unfold pa450010cl
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h0 : pa450010wv b 4 pa450010wTX[0]! = pT := by
    have e : pa450010gK b 3 = pT := by simp [pa450010gK]
    rw [← e, ← pa450010wv_wK b 3 (by norm_num)]
    rfl
  have h1 : pa450010wv b 4 pa450010wTX[1]! = pa450010x := pa450010wv_wx b (by norm_num)
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj2 : j < 2 := hj
    interval_cases j
    · exact Or.inl h0
    · exact Or.inr h1
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, h0⟩
    · exact ⟨1, by decide, h1⟩

theorem pa450010_Y_of {b : Bool} {k cnt kY cntY kT cntT : ℕ}
    {G GI T PL POS SRT SRI GY GIY TY PLY POSY SRTY SRIY GT GIT TT PLT POST SRTT SRIT PZ : ℕ → ℕ}
    (hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 960 k G GI cnt T PL 4
      (pa450010S b) (pa450010SI b) pa450010wCKX = true)
    (hsl : penumSlK 28 5 (mask 5) (28 * 5) false G GI k cnt T PL POS SRT SRI 0 960 = true)
    (hdY : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 8 kY GY GIY cntY TY PLY 4
      (pa450010S b) (pa450010SI b) pa450010wY = true)
    (hslY : penumSlK 28 5 (mask 5) (28 * 5) false GY GIY kY cntY TY PLY POSY SRTY SRIY 0 8 =
      true)
    (hdT : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 4 kT GT GIT cntT TT PLT 4
      (pa450010S b) (pa450010SI b) pa450010wTX = true)
    (hslT : penumSlK 28 5 (mask 5) (28 * 5) false GT GIT kT cntT TT PLT POST SRTT SRIT 0 4 =
      true)
    (hcomm : allN 3 (fun j => centK 28 5 (mask 5) (28 * 5) kY GY (GY j)) = true)
    (hexp : bAnd(wordEqK 28 5 (mask 5) (pidn 28 5) GY GIY 3 [1, 1, 1, 1] (pidn 28 5),
      bAnd(wordEqK 28 5 (mask 5) (pidn 28 5) GY GIY 3 [2, 2, 2, 2] (pidn 28 5),
      wordEqK 28 5 (mask 5) (pidn 28 5) GY GIY 3 [3, 3, 3, 3] (pidn 28 5))) = true)
    (hZ : filtInK 28 5 (mask 5) cntY TY 5 G cntT TT PZ = true) :
    (∀ a ∈ pa450010cl b 4 pa450010wY, ∀ c ∈ pa450010cl b 4 pa450010wY, a * c = c * a) ∧
    (∀ y ∈ pa450010cl b 4 pa450010wY, y ^ 4 = 1) ∧
    centralizer ((pa450010cl b 4 pa450010wCKX : Subgroup (Perm (Fin 28))) : Set (Perm (Fin 28))) ⊓
      pa450010cl b 4 pa450010wY ≤ closure ({pT, pa450010x} : Set (Perm (Fin 28))) := by
  obtain ⟨xK, -, -, -, -, hk, hg, -⟩ := pa450010_rec (by norm_num) hd hsl
  obtain ⟨xY, hxY, -, hmemY, -, hkY, hgY, hgiY⟩ := pa450010_rec (by norm_num) hdY hslY
  obtain ⟨xT, hxT, -, hmemT, -, -, -, -⟩ := pa450010_rec (by norm_num) hdT hslT
  have hk3 : kY = 3 := hkY
  subst hk3
  have hk5 : k = 5 := hk
  subst hk5
  set Y := pa450010cl b 4 pa450010wY with hYdef
  have hYc : Y ≤ centralizer (Y : Set (Perm (Fin 28))) := by
    rw [hYdef, pa450010cl, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj3 : j < 3 := hj
    have h := closure_le_centralizer (by norm_num) hgY (hgY j hj3) (allN_iff.1 hcomm j hj3)
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h' hh'
    exact mem_centralizer_singleton_iff.1 (h hh')
  have hab : ∀ a ∈ Y, ∀ c ∈ Y, a * c = c * a := fun a ha c hc =>
    mem_centralizer_iff.1 (hYc hc) a ha
  refine ⟨hab, ?_, ?_⟩
  ·
    have hgen : ∀ j < 3, pa450010wv b 4 pa450010wY[j]! ^ 4 = 1 := by
      simp only [bAnd_eq, Bool.and_eq_true] at hexp
      obtain ⟨e1, e2, e3⟩ := hexp
      intro j hj
      have hp := fun {wd : List Int}
          (hw : wordEqK 28 5 (mask 5) (pidn 28 5) GY GIY 3 wd (pidn 28 5) = true) =>
        CFSG.KC.OrbGroup.prep_eq (pa450010_wordEq hgY hgiY hw)
          (prep_pidn (by norm_num) (by norm_num))
      interval_cases j
      · simpa [CFSG.Monster.B.Co2.toLetters, Quiver.SchreierGraph.evalWord_cons_true,
          Quiver.SchreierGraph.evalWord_nil, pow_succ, mul_assoc] using hp e1
      · simpa [CFSG.Monster.B.Co2.toLetters, Quiver.SchreierGraph.evalWord_cons_true,
          Quiver.SchreierGraph.evalWord_nil, pow_succ, mul_assoc] using hp e2
      · simpa [CFSG.Monster.B.Co2.toLetters, Quiver.SchreierGraph.evalWord_cons_true,
          Quiver.SchreierGraph.evalWord_nil, pow_succ, mul_assoc] using hp e3
    intro y hy
    rw [hYdef, pa450010cl] at hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact hgen j hj
    | one => exact one_pow 4
    | mul x z hx hz ihx ihz =>
      rw [(Commute.mul_pow (hab x hx z hz) 4), ihx, ihz, one_mul]
    | inv x _ ihx => rw [inv_pow, ihx, inv_one]
  ·
    rintro g ⟨hgC, hgY⟩
    obtain ⟨q, hq, rfl⟩ := (hmemY _).1 hgY
    obtain ⟨q', hq', e⟩ := filtInK_spec (by norm_num) (by norm_num) hxY hxT hg hZ q hq
      fun j hj => (mem_centralizer_iff.1 hgC _ (pa450010_gen_mem b 4 pa450010wCKX hj)).symm
    rw [← pa450010_clTX]
    exact (hmemT _).2 ⟨q', hq', e⟩

theorem pa450010_rbcY (b : Bool) :
    (∀ a ∈ centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))),
      ∀ c ∈ centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))), a * c = c * a) ∧
    (∀ y ∈ centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))), y ^ 4 = 1) ∧
    centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))) ⊓ D28 = zpowers pa450010x ∧
    K28 b ⊓ normalizer (jOf D28 pa450010x : Set (Perm (Fin 28))) =
      K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) ∧
    centralizer ((K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))) :
        Subgroup (Perm (Fin 28))) : Set (Perm (Fin 28))) ⊓
        (centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) ⊓
          (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))))) =
      closure ({pT, pa450010x} : Set (Perm (Fin 28))) ∧
    ∃ o ∈ centralizer (jOf D28 pa450010x : Set (Perm (Fin 28))) ⊓
        (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))),
      ∃ n ∈ K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28))), n * o * n⁻¹ = o * pa450010x := by
  obtain ⟨hKeq, hJn, hYeq, -, -⟩ := pa450010_K_facts b
  have hY := (show _ from
    match b with
    | false => pa450010_Y_of pa450010_CKX1_hd pa450010_CKX1_sl pa450010_Y1_hd pa450010_Y1_sl
        pa450010_TX1_hd pa450010_TX1_sl pa450010_Y1_comm pa450010_Y1_exp pa450010_Z1_filt
    | true => pa450010_Y_of pa450010_CKX2_hd pa450010_CKX2_sl pa450010_Y2_hd pa450010_Y2_sl
        pa450010_TX2_hd pa450010_TX2_sl pa450010_Y2_comm pa450010_Y2_exp pa450010_Z2_filt :
    (∀ a ∈ pa450010cl b 4 pa450010wY, ∀ c ∈ pa450010cl b 4 pa450010wY, a * c = c * a) ∧
    (∀ y ∈ pa450010cl b 4 pa450010wY, y ^ 4 = 1) ∧
    centralizer ((pa450010cl b 4 pa450010wCKX : Subgroup (Perm (Fin 28))) : Set (Perm (Fin 28))) ⊓
      pa450010cl b 4 pa450010wY ≤ closure ({pT, pa450010x} : Set (Perm (Fin 28))))
  obtain ⟨hab, hexp, hZ⟩ := hY
  have hxK : pa450010x ∈ K28 b := D28_le_K28 b pa450010_x_memD
  have hJK := pa450010_J_le_Kx b
  have hxY : pa450010x ∈ centralizer (pa450010Jg : Set (Perm (Fin 28))) ⊓
      (K28 b ⊓ centralizer ({pa450010x} : Set (Perm (Fin 28)))) :=
    ⟨pa450010_x_mem_CJ, hxK, mem_centralizer_singleton_iff.2 rfl⟩
  rw [pa450010_jOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hYeq]
    exact hab
  · rw [hYeq]
    exact hexp
  ·
    apply le_antisymm
    · rintro g ⟨⟨hJ, -⟩, hD⟩
      rw [← pa450010_CDJ]
      exact ⟨hD, hJ⟩
    · rw [zpowers_le]
      exact ⟨hxY, pa450010_x_memD⟩
  ·
    apply le_antisymm
    · rintro k ⟨hk, hkN⟩
      refine ⟨hk, ?_⟩
      have hyJ : k * pa450010x * k⁻¹ ∈ centralizer (pa450010Jg : Set (Perm (Fin 28))) := by
        rw [mem_centralizer_iff]
        intro j hj
        have hj' : k⁻¹ * j * k⁻¹⁻¹ ∈ pa450010Jg := (mem_normalizer_iff.1 (inv_mem hkN) j).1 hj
        have c := mem_centralizer_iff.1 pa450010_x_mem_CJ _ hj'
        calc j * (k * pa450010x * k⁻¹) = k * (k⁻¹ * j * k⁻¹⁻¹ * pa450010x) * k⁻¹ := by group
          _ = k * (pa450010x * (k⁻¹ * j * k⁻¹⁻¹)) * k⁻¹ := by rw [c]
          _ = k * pa450010x * k⁻¹ * j := by group
      have hy : k * pa450010x * k⁻¹ ∈ zpowers pa450010x := by
        rw [← pa450010_CDJ]
        exact ⟨D28_conj b k hk _ pa450010_x_memD, hyJ⟩
      rcases pa450010_zpowers_x hy with h1 | h1
      · exfalso
        have hx1 : pa450010x = 1 := by
          calc pa450010x = k⁻¹ * (k * pa450010x * k⁻¹) * k := by group
            _ = 1 := by rw [h1]; group
        have ho := pa450010_x_order
        rw [hx1, orderOf_one] at ho
        omega
      · refine mem_centralizer_singleton_iff.2 ?_
        calc k * pa450010x = k * pa450010x * k⁻¹ * k := by group
          _ = pa450010x * k := by rw [h1]
    · rintro k hk
      exact ⟨hk.1, (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).1 hJn hk⟩
  ·
    apply le_antisymm
    · rw [hYeq, hKeq]
      exact hZ
    · rw [closure_le]
      rintro g (rfl | rfl)
      · refine ⟨mem_centralizer_iff.2 fun h hh => pT_commute_of_mem_K28 b h hh.1,
          mem_centralizer_iff.2 fun j hj => pT_commute_of_mem_K28 b j (hJK hj).1,
          pa450010_pT_mem b, mem_centralizer_singleton_iff.2 (pT_commute_of_mem_K28 b _ hxK).symm⟩
      · exact ⟨mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 hh.2, hxY⟩
  ·
    obtain ⟨c, hc, y, hy, e⟩ := pa450010_G3 b
    rw [pa450010_jOf_eq] at hy
    refine ⟨y, hy, c, hc, ?_⟩
    have hyx : y * pa450010x = pa450010x * y := mem_centralizer_singleton_iff.1 hy.2.2
    calc c * y * c⁻¹ = c * y * c⁻¹ * y⁻¹ * y := by group
      _ = pa450010x * y := by rw [e]
      _ = y * pa450010x := hyx.symm

end CertificateChecks.KernelPropA

end
