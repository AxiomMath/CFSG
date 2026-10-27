module

public import Certificates.Kernel.U52.NormEChk
public import Certificates.Kernel.U52.NormGlue
public import Certificates.Kernel.U52.BindF
public import CFSG.Certificates.Kernel.U52.NormESound
public import CFSG.Milestones.ASVolI.F48.Rest.G23Stab

public section

namespace CertificateChecks.KernelU52

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.WordF CFSG.KS.U52N CertificateChecks.KernelU52.N
  CertificateChecks.KernelU52.NE CertificateChecks.KernelU52F
open CFSG.Sporadic.HNOddCore
open scoped Pointwise

@[expose] noncomputable def u52neσ (i : ℕ) : Equiv.Perm (Fin 462) :=
  CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[i]!

theorem u52ne_pisL {i : ℕ} (hi : i < 5) :
    CFSG.ONSchreier.Native.pisInv 462 (burnsideF48t_u52eLArr ())[i]! (burnsideF48t_u52eLInv ())[i]! =
      true := by
  rw [lf_eq i hi, lfi_eq i hi]
  unfold CFSG.ONSchreier.Native.pisInv
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro j hj
  obtain ⟨-, -, h3⟩ := Raw.Orb.permOK_facts (allN_spec lfPerm i hi)
  rw [Raw.Orb.unpack_get hj, Raw.Orb.unpack_get (h3 j hj).1, (h3 j hj).2]
  simp [(h3 j hj).1]

theorem u52ne_recL : burnsideF48t_RecL 462 (burnsideF48t_u52eLArr ()) (burnsideF48t_u52eLInv ())
    (fun i : Fin 5 => u52neσ i) :=
  fun i => CFSG.ONSchreier.prep_permOfArr (u52ne_pisL i.2)

theorem u52ne_lpRep {c : ℕ} (hc : c < 5) : Raw.Orb.PRep 462 9 (LFP c) (u52neσ c) :=
  fun x => by
    rw [← Raw.Orb.unpack_get x.2, ← lf_eq c hc]
    exact (CFSG.ONSchreier.prep_permOfArr (u52ne_pisL hc)).1 x

theorem u52ne_evRep (wd : List (Fin 5 × Bool)) :
    Raw.Orb.PRep 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI wd)
      (burnsideF48s_ev (fun l : Fin 5 => u52neσ l) wd) := fun x => by
  rw [← Raw.Orb.unpack_get x.2, ← evF_eq]
  exact burnsideF48t_prep_evA u52ne_recL wd x

theorem u52ne_evFK_shr (wd : List (Fin 5 × Bool)) :
    evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI wd >>> (462 * 9) = 0 := by
  cases wd with
  | nil => exact CFSG.KS.PF.pidn_shr (by norm_num) (by norm_num)
  | cons l wd => exact CFSG.KS.PF.pcomp_shr (n := 462) (w := 9) _ _ (by norm_num) (by norm_num)

theorem u52ne_listsK : Lists 462 9 nKL burnsideF48t_u52K' := by
  refine ⟨fun k hk => ?_, fun P hP => ?_⟩
  · obtain ⟨m, hm, rfl⟩ := u52n_K_sub k hk
    refine ⟨nKL.getD m 0, ?_, u52n_kl_shr hm, u52n_klRep hm⟩
    rw [List.getD_eq_getElem _ _ (by rw [u52n_nKL_length]; exact hm)]
    exact List.getElem_mem _
  · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hP
    have hm9 : m < 9 := by rwa [u52n_nKL_length] at hm
    refine ⟨u52nκ m, u52n_κ_mem hm9, ?_⟩
    have := u52n_klRep hm9
    rwa [List.getD_eq_getElem _ _ hm] at this

@[expose] noncomputable def u52neκ (j m : ℕ) : Equiv.Perm (Fin 462) :=
  burnsideF48s_ev (fun l : Fin 5 => u52neσ l) ((burnsideF48t_u52eKhW.getD j []).getD m [])

theorem u52ne_khOK {j : ℕ} (hj : j < 4) :
    khOK 462 9 (mask 9) (pidn 462 9) (eKL j) nKL = true := allN_spec eKh j hj

theorem u52ne_eKL_length {j : ℕ} (hj : j < 4) : (eKL j).length = 18 := by
  have h := u52ne_khOK hj
  unfold khOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.1.1

theorem u52ne_KhW_length {j : ℕ} (hj : j < 4) : (burnsideF48t_u52eKhW.getD j []).length = 18 := by
  have := u52ne_eKL_length hj
  rwa [eKL, List.length_map] at this

theorem u52ne_klRep {j m : ℕ} (hj : j < 4) (hm : m < 18) :
    Raw.Orb.PRep 462 9 ((eKL j).getD m 0) (u52neκ j m) := by
  rw [eKL, u52n_getD_map _ _ [] (by rw [u52ne_KhW_length hj]; exact hm)]
  exact u52ne_evRep _

theorem u52ne_kl_shr {j m : ℕ} (hj : j < 4) (hm : m < 18) : (eKL j).getD m 0 >>> (462 * 9) = 0 := by
  rw [eKL, u52n_getD_map _ _ [] (by rw [u52ne_KhW_length hj]; exact hm)]
  exact u52ne_evFK_shr _

@[expose] def u52neGen (s : ℕ) : ℕ := [1, 3, 9].getD s 0

theorem u52ne_KG_size (j : ℕ) : (burnsideF48t_u52eKG j ()).size = 3 := by
  simp [burnsideF48t_u52eKG]

theorem u52ne_KGRep {j : ℕ} (hj : j < 4) : ∀ s < (burnsideF48t_u52eKG j ()).size,
    CFSG.ONSchreier.PRep 462 (burnsideF48t_u52eKG j ())[s]! (u52neκ j (u52neGen s)) := by
  intro s hs
  rw [u52ne_KG_size] at hs
  have e : (burnsideF48t_u52eKG j ())[s]! =
      (burnsideF48t_u52eKL j ()).getD (u52neGen s) (CFSG.ONSchreier.Native.pid 462) := by
    interval_cases s <;> rfl
  have hlt : u52neGen s < (burnsideF48t_u52eKhW.getD j []).length := by
    rw [u52ne_KhW_length hj]
    interval_cases s <;> decide
  rw [e]
  have := burnsideF48t_prep_evA u52ne_recL ((burnsideF48t_u52eKhW.getD j []).getD (u52neGen s) [])
  simp only [burnsideF48t_u52eKL]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map]
  unfold u52neκ
  rw [List.getD_eq_getElem _ _ hlt] at this ⊢
  exact this

theorem u52ne_K'_eq {j : ℕ} (hj : j < 4) : arrGen 462 (burnsideF48t_u52eKG j ()) =
    Subgroup.closure (Set.range fun s : Fin (burnsideF48t_u52eKG j ()).size =>
      u52neκ j (u52neGen s)) :=
  arrGen_eq (σ := fun s => u52neκ j (u52neGen s)) (u52ne_KGRep hj)

theorem u52ne_gen_mem {j : ℕ} (hj : j < 4) {s : ℕ} (hs : s < 3) :
    u52neκ j (u52neGen s) ∈ arrGen 462 (burnsideF48t_u52eKG j ()) := by
  rw [u52ne_K'_eq hj]
  exact Subgroup.subset_closure ⟨⟨s, by rw [u52ne_KG_size]; exact hs⟩, rfl⟩

theorem u52ne_kfacts {j : ℕ} (hj : j < 4) :
    (∃ m < 18, u52neκ j m = 1) ∧
    (∀ m < 18, ∀ s < 3, ∃ m' < 18, u52neκ j m * u52neκ j (u52neGen s) = u52neκ j m') ∧
    (∀ i < 9, u52neκ j i = u52nκ i ∧ u52neκ j (i + 9) = u52neκ j 9 * u52nκ i) ∧
    (∀ m < 18, u52neκ j m * u52neκ j m ∈ burnsideF48t_u52K') := by
  obtain ⟨-, h1, h2, h3, h4⟩ := khOK_sound (by norm_num) (by norm_num) u52ne_listsK
    (fun m hm => u52ne_klRep hj (by rwa [u52ne_eKL_length hj] at hm)) (fun i hi => u52n_klRep hi)
    (u52ne_khOK hj)
  exact ⟨h1, h2, h3, h4⟩

theorem u52ne_K_le {j : ℕ} (hj : j < 4) :
    burnsideF48t_u52K' ≤ arrGen 462 (burnsideF48t_u52eKG j ()) := by
  obtain ⟨-, -, h3, -⟩ := u52ne_kfacts hj
  rw [u52n_K'_eq, Subgroup.closure_le]
  rintro _ ⟨⟨s, hs⟩, rfl⟩
  have hs2 : s < 2 := u52n_KArr_size ▸ hs
  interval_cases s
  · have := u52ne_gen_mem hj (s := 0) (by norm_num)
    rw [show u52neGen 0 = 1 from rfl, (h3 1 (by norm_num)).1] at this
    exact this
  · have := u52ne_gen_mem hj (s := 1) (by norm_num)
    rw [show u52neGen 1 = 3 from rfl, (h3 3 (by norm_num)).1] at this
    exact this

theorem u52ne_κ_mem {j m : ℕ} (hj : j < 4) (hm : m < 18) :
    u52neκ j m ∈ arrGen 462 (burnsideF48t_u52eKG j ()) := by
  obtain ⟨-, -, h3, -⟩ := u52ne_kfacts hj
  by_cases h9 : m < 9
  · rw [(h3 m h9).1]
    exact u52ne_K_le hj (u52n_κ_mem h9)
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 9 := ⟨m - 9, by omega⟩
    rw [(h3 m' (by omega)).2]
    exact Subgroup.mul_mem _ (u52ne_gen_mem hj (s := 2) (by norm_num))
      (u52ne_K_le hj (u52n_κ_mem (by omega)))

theorem u52ne_K_sub {j : ℕ} (hj : j < 4) :
    ∀ c ∈ arrGen 462 (burnsideF48t_u52eKG j ()), ∃ m < 18, c = u52neκ j m := by
  intro c hc
  obtain ⟨⟨m1, hm1, h1⟩, hcl, -, -⟩ := u52ne_kfacts hj
  rw [u52ne_K'_eq hj] at hc
  exact CFSG.Quasithin.closure_subset_of_right_closed (P := {g | ∃ m < 18, g = u52neκ j m})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩) ⟨m1, hm1, h1.symm⟩
    (by
      rintro p ⟨m, hm, rfl⟩ _ ⟨s, rfl⟩
      have hs : (s : ℕ) < 3 := lt_of_lt_of_eq s.2 (u52ne_KG_size j)
      obtain ⟨m', hm', he⟩ := hcl m hm s hs
      exact ⟨m', hm', he⟩)
    hc

theorem u52ne_lists {j : ℕ} (hj : j < 4) :
    Lists 462 9 (eKL j) (arrGen 462 (burnsideF48t_u52eKG j ())) := by
  refine ⟨fun k hk => ?_, fun P hP => ?_⟩
  · obtain ⟨m, hm, rfl⟩ := u52ne_K_sub hj k hk
    refine ⟨(eKL j).getD m 0, ?_, u52ne_kl_shr hj hm, u52ne_klRep hj hm⟩
    rw [List.getD_eq_getElem _ _ (by rw [u52ne_eKL_length hj]; exact hm)]
    exact List.getElem_mem _
  · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hP
    have hm18 : m < 18 := by rwa [u52ne_eKL_length hj] at hm
    refine ⟨u52neκ j m, u52ne_κ_mem hj hm18, ?_⟩
    have := u52ne_klRep hj hm18
    rwa [List.getD_eq_getElem _ _ hm] at this

theorem u52ne_gens {j : ℕ} (hj : j < 4) :
    ∀ g ∈ khG (eKL j), ∃ k ∈ arrGen 462 (burnsideF48t_u52eKG j ()), Raw.Orb.PRep 462 9 g k := by
  intro g hg
  simp only [khG, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨_, u52ne_κ_mem hj (m := 1) (by norm_num), u52ne_klRep hj (by norm_num)⟩
  · exact ⟨_, u52ne_κ_mem hj (m := 3) (by norm_num), u52ne_klRep hj (by norm_num)⟩
  · exact ⟨_, u52ne_κ_mem hj (m := 9) (by norm_num), u52ne_klRep hj (by norm_num)⟩

theorem u52ne_normK {j : ℕ} (hj : j < 4) {x : Equiv.Perm (Fin 462)}
    (hx : ∀ k ∈ arrGen 462 (burnsideF48t_u52eKG j ()),
      x * k * x⁻¹ ∈ arrGen 462 (burnsideF48t_u52eKG j ())) :
    ∀ k ∈ burnsideF48t_u52K', x * k * x⁻¹ ∈ burnsideF48t_u52K' := by
  intro k hk
  obtain ⟨-, -, -, hsq⟩ := u52ne_kfacts hj
  set y := x * k * x⁻¹ with hy
  obtain ⟨m, hm, hym⟩ := u52ne_K_sub hj y (hx k (u52ne_K_le hj hk))
  have hyy : y * y ∈ burnsideF48t_u52K' := by rw [hym]; exact hsq m hm
  have hk9 : k ^ 9 = 1 := by
    have h := pow_card_eq_one' (G := ↥burnsideF48t_u52K') (x := ⟨k, hk⟩)
    rw [burnsideF48t_u52_card_K'] at h
    exact congrArg Subtype.val h
  have hy9 : y ^ 9 = 1 := by rw [hy, conj_pow, hk9, mul_one, mul_inv_cancel]
  have e : y = (y * y) ^ 5 := by
    rw [← sq, ← pow_mul, show 2 * 5 = 9 + 1 from rfl, pow_succ, hy9, one_mul]
  rw [e]
  exact Subgroup.pow_mem _ hyy 5

theorem u52ne_ff : u52neσ 4 * u52neσ 4 = 1 := by
  have h := eF
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  refine PRep.unique' (Raw.Orb.prep_pcomp (by norm_num) (u52ne_lpRep (by norm_num))
    (u52ne_lpRep (by norm_num))) ?_
  rw [h.1]
  exact Raw.Orb.prep_pidn (by norm_num) (by norm_num)

theorem u52ne_f_inv : (u52neσ 4)⁻¹ = u52neσ 4 := inv_eq_of_mul_eq_one_right u52ne_ff

theorem u52ne_f_normK :
    ∀ k ∈ burnsideF48t_u52K', u52neσ 4 * k * (u52neσ 4)⁻¹ ∈ burnsideF48t_u52K' := by
  have h := eF
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hle : burnsideF48t_u52K' ≤ burnsideF48t_u52K'.comap (MulAut.conj (u52neσ 4)).toMonoidHom := by
    conv_lhs => rw [u52n_K'_eq]
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨s, hs⟩, rfl⟩
    have hs2 : s < 2 := u52n_KArr_size ▸ hs
    have hg : nKL.getD (burnsideF48t_u52KGenIdx.getD s 0) 0 ∈ nKG := by
      interval_cases s <;> simp [nKG, burnsideF48t_u52KGenIdx]
    have hm := h.2 _ hg
    have hidx : burnsideF48t_u52KGenIdx.getD s 0 < 9 := by interval_cases s <;> decide
    have hrep := Raw.Orb.prep_pcomp (by norm_num) (Raw.Orb.prep_pcomp (by norm_num)
      (u52ne_lpRep (c := 4) (by norm_num)) (u52n_klRep hidx)) (u52ne_lpRep (c := 4) (by norm_num))
    have := u52ne_listsK.mem hrep hm
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change u52neσ 4 * u52nκ (burnsideF48t_u52KGenIdx.getD s 0) * (u52neσ 4)⁻¹ ∈ _
    rw [u52ne_f_inv]
    exact this
  intro k hk
  exact hle hk

theorem u52ne_f_mul_normK {x : Equiv.Perm (Fin 462)}
    (hx : ∀ k ∈ burnsideF48t_u52K', x * k * x⁻¹ ∈ burnsideF48t_u52K') :
    ∀ k ∈ burnsideF48t_u52K', (u52neσ 4 * x) * k * (u52neσ 4 * x)⁻¹ ∈ burnsideF48t_u52K' := by
  intro k hk
  have e : (u52neσ 4 * x) * k * (u52neσ 4 * x)⁻¹ = u52neσ 4 * (x * k * x⁻¹) * (u52neσ 4)⁻¹ := by
    group
  rw [e]
  exact u52ne_f_normK _ (hx k hk)

theorem u52ne_listed {H : Subgroup (Equiv.Perm (Fin 462))}
    {ok : ℕ → Bool} (hok : ∀ c, ok c = true → c < 4 ∧ burnsideF48t_u52σ c ∈ H)
    {nodes : List (List ℕ)} {par gen : List ℕ}
    (htree : treeOK 462 9 (mask 9) LP ok NF nodes par gen = true)
    {SV : List ℕ} {SW EW : List (List ℕ)}
    (hgens : gensOK 462 9 (mask 9) (pidn 462 9) LP ok SV SW = true)
    (hstab : stabOK 462 9 (mask 9) (pidn 462 9) NF SV EW = true)
    (hcard : Nat.card H = nodes.length * EW.length)
    {x : Equiv.Perm (Fin 462)} (hx : x ∈ H)
    (hxK : ∀ k ∈ burnsideF48t_u52K', x * k * x⁻¹ ∈ burnsideF48t_u52K') :
    ∃ i < EW.length, Raw.Orb.PRep 462 9 ((elems 462 9 (mask 9) (pidn 462 9) SV EW).getD i 0) x := by
  classical
  have hg : ∀ c, ok c = true → Raw.Orb.PRep 462 9 (LP c) (burnsideF48t_u52σ c) :=
    fun c hc => u52n_lpRep (hok c hc).1
  obtain ⟨-, hG⟩ := gensOK_sound (by norm_num) (by norm_num) hg hgens
  obtain ⟨hrep, hlt, hmaps, hinj⟩ := stabOK_sound (by norm_num) (by norm_num)
    (sv := fun j => ((SW.getD j []).map burnsideF48t_u52σ).prod) (fun j hj => (hG j hj).1) hstab
  set e : ℕ → Equiv.Perm (Fin 462) := fun i =>
    ((EW.getD i []).map fun j => ((SW.getD j []).map burnsideF48t_u52σ).prod).prod with he_def
  have heH : ∀ i < EW.length, e i ∈ H := by
    intro i hi
    rw [he_def]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    refine Subgroup.list_prod_mem _ fun z hz => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    exact (hok l ((hG c (hlt i hi c hc)).2 l hl)).2
  have heS : ∀ i < EW.length,
      e i ∈ MulAction.stabilizer (Equiv.Perm (Fin 462)) (finOf 462 NF) :=
    fun i hi => mem_stabilizer_of_maps fun p hp => mem_finOf.2 (hmaps i hi p (mem_finOf.1 hp))
  obtain ⟨S, hScard, hS⟩ := treeOK_sound (by norm_num) (by norm_num) H
    (fun c hc => ⟨hg c hc, (hok c hc).2⟩) htree
  have hbound := card_mul_card_inf_stab_le H (finOf 462 NF) S hS
  rw [hScard, hcard] at hbound
  have hpos : 0 < nodes.length := by
    have : 0 < Nat.card H := Nat.card_pos
    rw [hcard] at this
    exact Nat.pos_of_mul_pos_right this
  have hle := Nat.le_of_mul_le_mul_left hbound hpos
  have hxS : x ∈ MulAction.stabilizer (Equiv.Perm (Fin 462)) (finOf 462 NF) := by
    rw [← u52n_fixSet]
    exact mem_stabilizer_fixSet hxK
  have hxE : ∃ i < EW.length, x = e i := by
    by_contra hne
    have hnot : x ∉ (Finset.range EW.length).image e := by
      rw [Finset.mem_image]
      rintro ⟨i, hi, he⟩
      exact hne ⟨i, Finset.mem_range.1 hi, he.symm⟩
    have hTcard : (insert x ((Finset.range EW.length).image e)).card = EW.length + 1 := by
      rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn
        (fun i hi j hj hij => hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij),
        Finset.card_range]
    have hTsub : ((insert x ((Finset.range EW.length).image e) : Finset _) :
        Set (Equiv.Perm (Fin 462))) ⊆
        ((H ⊓ MulAction.stabilizer (Equiv.Perm (Fin 462)) (finOf 462 NF) :
          Subgroup (Equiv.Perm (Fin 462))) : Set (Equiv.Perm (Fin 462))) := by
      intro y hy
      rw [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff] at hy
      rcases hy with rfl | ⟨i, hi, rfl⟩
      · exact ⟨hx, hxS⟩
      · exact ⟨heH i (Finset.mem_range.1 hi), heS i (Finset.mem_range.1 hi)⟩
    have hc := Nat.card_mono (Set.toFinite _) hTsub
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hTcard] at hc
    have hc' : EW.length + 1 ≤
        Nat.card ↥(H ⊓ MulAction.stabilizer (Equiv.Perm (Fin 462)) (finOf 462 NF)) := hc
    omega
  obtain ⟨i, hi, rfl⟩ := hxE
  exact ⟨i, hi, (hrep i hi).1⟩

theorem u52ne_getD_mem {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

theorem u52ne_okP1 (c : ℕ) (hc : okP1 c = true) : c < 4 ∧ burnsideF48t_u52σ c ∈ burnsideF48t_u52P1' := by
  have hc3 : c < 3 := by simpa [okP1, Nat.blt_eq] using hc
  exact ⟨by omega, u52n_σ_mem_P1 hc3⟩

theorem u52ne_okP2 (c : ℕ) (hc : okP2 c = true) : c < 4 ∧ burnsideF48t_u52σ c ∈ burnsideF48t_u52P2' := by
  have hc' : c < 2 ∨ c = 3 := by
    simp only [okP2, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
    exact hc
  exact ⟨by omega, u52n_σ_mem_P2 hc'⟩

theorem u52ne_okB (c : ℕ) (hc : okB c = true) : c < 4 ∧ burnsideF48t_u52σ c ∈ burnsideF48t_u52B' := by
  have hc2 : c < 2 := by simpa [okB, Nat.blt_eq] using hc
  refine ⟨by omega, Subgroup.subset_closure ⟨c, by simpa [burnsideF48t_u52BArr] using hc2, ?_⟩⟩
  refine permOfArr_eq_of_prep ?_
  have e : burnsideF48t_u52BArr[c]! = burnsideF48t_u52LArr[c]! := by
    interval_cases c <;> rfl
  rw [e]
  exact (CFSG.ONSchreier.prep_permOfArr (u52n_pisL (by omega))).1

theorem u52ne_cases {H : Subgroup (Equiv.Perm (Fin 462))}
    {ok : ℕ → Bool} (hok : ∀ c, ok c = true → c < 4 ∧ burnsideF48t_u52σ c ∈ H)
    {nodes : List (List ℕ)} {par gen : List ℕ}
    (htree : treeOK 462 9 (mask 9) LP ok NF nodes par gen = true)
    {SV : List ℕ} {SW EW : List (List ℕ)}
    (hgens : gensOK 462 9 (mask 9) (pidn 462 9) LP ok SV SW = true)
    (hstab : stabOK 462 9 (mask 9) (pidn 462 9) NF SV EW = true)
    (hcard : Nat.card H = nodes.length * EW.length)
    {x : Equiv.Perm (Fin 462)} (hx : x ∈ H ∨ u52neσ 4 * x ∈ H)
    (hxK : ∀ k ∈ burnsideF48t_u52K', x * k * x⁻¹ ∈ burnsideF48t_u52K') :
    ∃ E ∈ elems 462 9 (mask 9) (pidn 462 9) SV EW,
      Raw.Orb.PRep 462 9 E x ∨ Raw.Orb.PRep 462 9 (pcomp 462 9 (mask 9) (LFP 4) E) x := by
  have hlen : ∀ i < EW.length, i < (elems 462 9 (mask 9) (pidn 462 9) SV EW).length := fun i hi => by
    simpa [elems] using hi
  rcases hx with hx | hx
  · obtain ⟨i, hi, hE⟩ := u52ne_listed hok htree hgens hstab hcard hx hxK
    exact ⟨_, u52ne_getD_mem (hlen i hi), Or.inl hE⟩
  · obtain ⟨i, hi, hE⟩ := u52ne_listed hok htree hgens hstab hcard hx (u52ne_f_mul_normK hxK)
    refine ⟨_, u52ne_getD_mem (hlen i hi), Or.inr ?_⟩
    have := Raw.Orb.prep_pcomp (by norm_num) (u52ne_lpRep (c := 4) (by norm_num)) hE
    rwa [← mul_assoc, u52ne_ff, one_mul] at this

theorem u52ne_risRep {RW : List (List (Fin 5 × Bool))} {r : ℕ}
    (hr : r ∈ RW.map fun w => evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI (burnsideF48s_eInvW w)) :
    ∃ w ∈ RW, Raw.Orb.PRep 462 9 r (burnsideF48s_ev (fun l : Fin 5 => u52neσ l) w)⁻¹ := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  refine ⟨w, hw, ?_⟩
  rw [← burnsideF48s_e_ev_invW]
  exact u52ne_evRep _

theorem u52ne_hat {j fix : ℕ} (hj : j < 4) (hfix : fix < 462)
    {RW : List (List (Fin 5 × Bool))} {E : ℕ} {x : Equiv.Perm (Fin 462)}
    (hE : Raw.Orb.PRep 462 9 E x)
    (h : hatT 462 9 (mask 9) fix (eKL j)
      (RW.map fun w => evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI (burnsideF48s_eInvW w)) E = true)
    (hxfix : x ⟨fix, hfix⟩ ≠ ⟨fix, hfix⟩)
    (hxH : ∀ k ∈ arrGen 462 (burnsideF48t_u52eKG j ()),
      x * k * x⁻¹ ∈ arrGen 462 (burnsideF48t_u52eKG j ()))
    (hxx : x * x ∈ arrGen 462 (burnsideF48t_u52eKG j ())) :
    ∃ w ∈ RW, (burnsideF48s_ev (fun l : Fin 5 => u52neσ l) w)⁻¹ * x ∈
      arrGen 462 (burnsideF48t_u52eKG j ()) := by
  obtain ⟨r, hr, hρ⟩ := hatT_sound (by norm_num) (by norm_num) hfix (u52ne_lists hj) (u52ne_gens hj)
    hE h hxfix hxH hxx
  obtain ⟨w, hw, hrw⟩ := u52ne_risRep hr
  exact ⟨w, hw, hρ _ hrw⟩

theorem u52ne_test1 (x : Equiv.Perm (Fin 462))
    (hx : x ∈ burnsideF48t_u52P1' ∨ u52neσ 4 * x ∈ burnsideF48t_u52P1')
    (hfix : x ⟨165, by norm_num⟩ ≠ ⟨165, by norm_num⟩) (j : ℕ) (hj : j < 3)
    (hxH : ∀ k ∈ arrGen 462 (burnsideF48t_u52eKG j ()),
      x * k * x⁻¹ ∈ arrGen 462 (burnsideF48t_u52eKG j ()))
    (hxx : x * x ∈ arrGen 462 (burnsideF48t_u52eKG j ())) :
    j = 2 ∧ ∃ w ∈ burnsideF48t_u52eXW, (burnsideF48s_ev (fun l : Fin 5 => u52neσ l) w)⁻¹ * x ∈
      arrGen 462 (burnsideF48t_u52eKG 2 ()) := by
  obtain ⟨-, hl1, -, -, hl2, -, -, -, -, -, -⟩ := nPref
  obtain ⟨E, hEm, hE⟩ := u52ne_cases u52ne_okP1 nTreeP1 nGensP1 nStabP1
    (by rw [burnsideF48t_u52_card_P1', hl1, hl2]) hx (u52ne_normK (by omega) hxH)
  have hall := List.all_eq_true.1 eT1 E hEm
  simp only [Bool.and_eq_true] at hall
  obtain ⟨E', hE', ht⟩ : ∃ E', Raw.Orb.PRep 462 9 E' x ∧ eTest1 E' = true := by
    rcases hE with hE | hE
    · exact ⟨E, hE, hall.1⟩
    · exact ⟨_, hE, hall.2⟩
  unfold eTest1 at ht
  simp only [Bool.and_eq_true] at ht
  obtain ⟨⟨t0, t1⟩, t2⟩ := ht
  interval_cases j
  · obtain ⟨w, hw, -⟩ := u52ne_hat (RW := []) (by norm_num) (by norm_num) hE' t0 hfix hxH hxx
    exact absurd hw List.not_mem_nil
  · obtain ⟨w, hw, -⟩ := u52ne_hat (RW := []) (by norm_num) (by norm_num) hE' t1 hfix hxH hxx
    exact absurd hw List.not_mem_nil
  · exact ⟨rfl, u52ne_hat (by norm_num) (by norm_num) hE' t2 hfix hxH hxx⟩

theorem u52ne_test2 (x : Equiv.Perm (Fin 462))
    (hx : x ∈ burnsideF48t_u52P2' ∨ u52neσ 4 * x ∈ burnsideF48t_u52P2')
    (hfix : x ⟨0, by norm_num⟩ ≠ ⟨0, by norm_num⟩) (j : ℕ) (hj : j = 2 ∨ j = 3)
    (hxH : ∀ k ∈ arrGen 462 (burnsideF48t_u52eKG j ()),
      x * k * x⁻¹ ∈ arrGen 462 (burnsideF48t_u52eKG j ()))
    (hxx : x * x ∈ arrGen 462 (burnsideF48t_u52eKG j ())) :
    j = 2 ∧ ∃ w ∈ burnsideF48t_u52eYW, (burnsideF48s_ev (fun l : Fin 5 => u52neσ l) w)⁻¹ * x ∈
      arrGen 462 (burnsideF48t_u52eKG 2 ()) := by
  obtain ⟨-, -, hl1, -, -, hl2, -, -, -, -, -⟩ := nPref
  obtain ⟨E, hEm, hE⟩ := u52ne_cases u52ne_okP2 nTreeP2 nGensP2 nStabP2
    (by rw [burnsideF48t_u52_card_P2', hl1, hl2]) hx (u52ne_normK (by omega) hxH)
  have hall := List.all_eq_true.1 eT2 E hEm
  simp only [Bool.and_eq_true] at hall
  obtain ⟨E', hE', ht⟩ : ∃ E', Raw.Orb.PRep 462 9 E' x ∧ eTest2 E' = true := by
    rcases hE with hE | hE
    · exact ⟨E, hE, hall.1⟩
    · exact ⟨_, hE, hall.2⟩
  unfold eTest2 at ht
  simp only [Bool.and_eq_true] at ht
  obtain ⟨t2, t3⟩ := ht
  rcases hj with rfl | rfl
  · exact ⟨rfl, u52ne_hat (by norm_num) (by norm_num) hE' t2 hfix hxH hxx⟩
  · obtain ⟨w, hw, -⟩ := u52ne_hat (RW := []) (by norm_num) (by norm_num) hE' t3 hfix hxH hxx
    exact absurd hw List.not_mem_nil

theorem u52ne_S0 : ∀ c < nS0.length, ∃ s ∈ burnsideF48t_u52S0',
    Raw.Orb.PRep 462 9 (nS0.getD c 0) s := by
  intro c hc
  have hcl : c < burnsideF48t_u52SW.length := by simpa [nS0] using hc
  refine ⟨burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) (burnsideF48t_u52SW.getD c []),
    ?_, ?_⟩
  · have ht : burnsideF48t_evA 462 burnsideF48t_u52LArr (burnsideF48t_u52LInv ())
        (burnsideF48t_u52SW.getD c []) ∈ burnsideF48t_u52S0Arr () := by
      simp only [burnsideF48t_u52S0Arr, List.mem_toArray, List.mem_map]
      exact ⟨_, by rw [List.getD_eq_getElem _ _ hcl]; exact List.getElem_mem _, rfl⟩
    have := burnsideF48t_permOfArr_mem_arrGen (N := 462) ht
    rwa [permOfArr_eq_of_prep (burnsideF48t_prep_evA u52n_recL _)] at this
  · rw [nS0, u52n_getD_map _ _ [] hcl]
    exact u52n_evRep _

theorem u52ne_listedB {β : Equiv.Perm (Fin 462)}
    (hβ : β ∈ burnsideF48t_u52B')
    (hβK : ∀ k ∈ burnsideF48t_u52K', β * k * β⁻¹ ∈ burnsideF48t_u52K') :
    ∃ i < 36, Raw.Orb.PRep 462 9 ((elems 462 9 (mask 9) (pidn 462 9) SVB EWB).getD i 0) β := by
  obtain ⟨hl1, -, -, hl2, -⟩ := nPref
  obtain ⟨i, hi, hE⟩ := u52ne_listed u52ne_okB nTreeB nGensB nStabB
    (by rw [burnsideF48t_u52_card_B', hl1, hl2]) hβ hβK
  exact ⟨i, hl2 ▸ hi, hE⟩

theorem u52ne_testB {β : Equiv.Perm (Fin 462)}
    (hβ : β ∈ burnsideF48t_u52B')
    (hβK : ∀ k ∈ burnsideF48t_u52K', β * k * β⁻¹ ∈ burnsideF48t_u52K')
    (hββ : β * β ∈ burnsideF48t_u52K') (hnot : β ∉ burnsideF48t_u52K') :
    ∃ k ∈ burnsideF48t_u52K', β * k ∈ burnsideF48t_u52S0' ∧ β * k ≠ 1 := by
  obtain ⟨i, hi, hE⟩ := u52ne_listedB hβ hβK
  obtain ⟨-, -, h⟩ := eTB
  have h1 := allN_spec h i hi
  simp only [Bool.and_eq_true] at h1
  exact hatB_sound (by norm_num) (by norm_num) u52ne_listsK u52ne_S0 hE h1.1 hββ hnot

theorem u52ne_testF {β : Equiv.Perm (Fin 462)}
    (hβ : β ∈ burnsideF48t_u52B')
    (htK : ∀ k ∈ burnsideF48t_u52K', (u52neσ 4 * β) * k * (u52neσ 4 * β)⁻¹ ∈ burnsideF48t_u52K')
    (htt : (u52neσ 4 * β) * (u52neσ 4 * β) ∈ burnsideF48t_u52K') :
    ∃ j < 4, u52neσ 4 * β ∈ arrGen 462 (burnsideF48t_u52eKG j ()) := by
  have hβK : ∀ k ∈ burnsideF48t_u52K', β * k * β⁻¹ ∈ burnsideF48t_u52K' := by
    have := u52ne_f_mul_normK htK
    rwa [← mul_assoc, u52ne_ff, one_mul] at this
  obtain ⟨i, hi, hE⟩ := u52ne_listedB hβ hβK
  obtain ⟨-, -, h⟩ := eTB
  have h1 := allN_spec h i hi
  simp only [Bool.and_eq_true] at h1
  have hF := Raw.Orb.prep_pcomp (by norm_num) (u52ne_lpRep (c := 4) (by norm_num)) hE
  obtain ⟨c, hc, hEc⟩ := hatF_sound (by norm_num) (by norm_num) u52ne_listsK hF h1.2 htt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have hm : ∀ j < 4, c = eKL j → u52neσ 4 * β ∈ arrGen 462 (burnsideF48t_u52eKG j ()) :=
    fun j hj hcj => (u52ne_lists hj).mem hF (memN_iff.2 (hcj ▸ hEc))
  rcases hc with hc | hc | hc | hc
  · exact ⟨0, by norm_num, hm 0 (by norm_num) hc⟩
  · exact ⟨1, by norm_num, hm 1 (by norm_num) hc⟩
  · exact ⟨2, by norm_num, hm 2 (by norm_num) hc⟩
  · exact ⟨3, by norm_num, hm 3 (by norm_num) hc⟩

end CertificateChecks.KernelU52

end
