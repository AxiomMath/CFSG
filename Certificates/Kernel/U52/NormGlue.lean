module

public import Certificates.Kernel.U52.NormChk
public import Certificates.Kernel.U52.Bind
public import CFSG.Certificates.Kernel.U52.NormSound
public import CFSG.Milestones.ASVolI.F48.Rest.U52Facts

public section

namespace CertificateChecks.KernelU52

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.WordF CFSG.KS.U52N CertificateChecks.KernelU52.N
open CFSG.Sporadic.HNOddCore
open scoped Pointwise

theorem u52n_pisL {i : ℕ} (hi : i < 4) :
    CFSG.ONSchreier.Native.pisInv 462 burnsideF48t_u52LArr[i]! (burnsideF48t_u52LInv ())[i]! =
      true := by
  rw [l_eq i hi, li_eq i hi]
  unfold CFSG.ONSchreier.Native.pisInv
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro j hj
  obtain ⟨-, -, h3⟩ := Raw.Orb.permOK_facts (allN_spec lpPerm i hi)
  rw [Raw.Orb.unpack_get hj, Raw.Orb.unpack_get (h3 j hj).1, (h3 j hj).2]
  simp [(h3 j hj).1]

theorem u52n_recL : burnsideF48t_RecL 462 burnsideF48t_u52LArr (burnsideF48t_u52LInv ())
    (fun i : Fin 4 => burnsideF48t_u52σ i) :=
  fun i => CFSG.ONSchreier.prep_permOfArr (u52n_pisL i.2)

theorem u52n_lpRep {c : ℕ} (hc : c < 4) : Raw.Orb.PRep 462 9 (LP c) (burnsideF48t_u52σ c) :=
  fun x => by
    rw [← Raw.Orb.unpack_get x.2, ← l_eq c hc]
    exact (CFSG.ONSchreier.prep_permOfArr (u52n_pisL hc)).1 x

theorem u52n_evRep (wd : List (Fin 4 × Bool)) :
    Raw.Orb.PRep 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LP LPI wd)
      (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) wd) := fun x => by
  rw [← Raw.Orb.unpack_get x.2, ← ev_eq]
  exact burnsideF48t_prep_evA u52n_recL wd x

theorem u52n_evFK_shr (wd : List (Fin 4 × Bool)) :
    evFK 462 9 (mask 9) (pidn 462 9) LP LPI wd >>> (462 * 9) = 0 := by
  cases wd with
  | nil => exact CFSG.KS.PF.pidn_shr (by norm_num) (by norm_num)
  | cons l wd => exact CFSG.KS.PF.pcomp_shr (n := 462) (w := 9) _ _ (by norm_num) (by norm_num)

theorem u52n_σ_mem_P1 {c : ℕ} (hc : c < 3) : burnsideF48t_u52σ c ∈ burnsideF48t_u52P1' := by
  refine Subgroup.subset_closure ⟨c, by simpa [burnsideF48t_u52P1Arr] using hc, ?_⟩
  refine permOfArr_eq_of_prep ?_
  have e : burnsideF48t_u52P1Arr[c]! = burnsideF48t_u52LArr[c]! := by
    interval_cases c <;> rfl
  rw [e]
  exact (CFSG.ONSchreier.prep_permOfArr (u52n_pisL (by omega))).1

theorem u52n_σ_mem_P2 {c : ℕ} (hc : c < 2 ∨ c = 3) :
    burnsideF48t_u52σ c ∈ burnsideF48t_u52P2' := by
  have hc4 : c < 4 := by omega
  have hrep := (CFSG.ONSchreier.prep_permOfArr (u52n_pisL hc4)).1
  rcases hc with hc | rfl
  · refine Subgroup.subset_closure ⟨c, by simp [burnsideF48t_u52P2Arr]; omega, ?_⟩
    refine permOfArr_eq_of_prep ?_
    have e : burnsideF48t_u52P2Arr[c]! = burnsideF48t_u52LArr[c]! := by
      interval_cases c <;> rfl
    rw [e]
    exact hrep
  · refine Subgroup.subset_closure ⟨2, by simp [burnsideF48t_u52P2Arr], ?_⟩
    refine permOfArr_eq_of_prep ?_
    have e : burnsideF48t_u52P2Arr[2]! = burnsideF48t_u52LArr[3]! := rfl
    rw [e]
    exact hrep

theorem u52n_getD_map {α : Type} (f : α → ℕ) (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

theorem u52n_KW_length : burnsideF48t_u52KW.length = 9 := rfl

theorem u52n_nKL_length : nKL.length = 9 := by
  rw [nKL, List.length_map, u52n_KW_length]

@[expose] noncomputable def u52nκ (m : ℕ) : Equiv.Perm (Fin 462) :=
  burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) (burnsideF48t_u52KW.getD m [])

theorem u52n_klRep {m : ℕ} (hm : m < 9) : Raw.Orb.PRep 462 9 (nKL.getD m 0) (u52nκ m) := by
  rw [nKL, u52n_getD_map _ _ [] (by rw [u52n_KW_length]; exact hm)]
  exact u52n_evRep _

theorem u52n_kl_shr {m : ℕ} (hm : m < 9) : nKL.getD m 0 >>> (462 * 9) = 0 := by
  rw [nKL, u52n_getD_map _ _ [] (by rw [u52n_KW_length]; exact hm)]
  exact u52n_evFK_shr _

theorem u52n_KArr_size : (burnsideF48t_u52KArr ()).size = 2 := by
  simp [burnsideF48t_u52KArr, burnsideF48t_u52KGenIdx]

theorem u52n_KArrRep : ∀ s < (burnsideF48t_u52KArr ()).size,
    CFSG.ONSchreier.PRep 462 (burnsideF48t_u52KArr ())[s]!
      (u52nκ (burnsideF48t_u52KGenIdx.getD s 0)) := by
  intro s hs
  have hs2 : s < 2 := u52n_KArr_size ▸ hs
  unfold burnsideF48t_u52KArr
  rw [getD_map_toArray _ _ 0 (by simpa [burnsideF48t_u52KGenIdx] using hs2)]
  exact burnsideF48t_prep_evA u52n_recL _

theorem u52n_K'_eq : burnsideF48t_u52K' = Subgroup.closure (Set.range
    fun s : Fin (burnsideF48t_u52KArr ()).size => u52nκ (burnsideF48t_u52KGenIdx.getD s 0)) :=
  arrGen_eq (σ := fun s => u52nκ (burnsideF48t_u52KGenIdx.getD s 0)) u52n_KArrRep

theorem u52n_kfacts :
    (∃ m < nKL.length, u52nκ m = 1) ∧
    (∀ m < nKL.length, ∀ j < nKG.length, ∃ m' < nKL.length,
      u52nκ m * u52nκ (burnsideF48t_u52KGenIdx.getD j 0) = u52nκ m') ∧
    (∀ x : Fin 462, (x : ℕ) ∈ NF ↔
      ∀ j < nKG.length, u52nκ (burnsideF48t_u52KGenIdx.getD j 0) x = x) := by
  refine kOK_sound (by norm_num) (by norm_num)
    (fun m hm => u52n_klRep (by rwa [u52n_nKL_length] at hm)) (fun j hj => ?_) nK
  have hj2 : j < 2 := hj
  interval_cases j
  · exact u52n_klRep (m := 1) (by norm_num)
  · exact u52n_klRep (m := 3) (by norm_num)

theorem u52n_K_sub : ∀ c ∈ burnsideF48t_u52K', ∃ m < 9, c = u52nκ m := by
  intro c hc
  obtain ⟨⟨m1, hm1, h1⟩, hcl, -⟩ := u52n_kfacts
  rw [u52n_K'_eq] at hc
  exact CFSG.Quasithin.closure_subset_of_right_closed (P := {g | ∃ m < 9, g = u52nκ m})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨m1, by rwa [u52n_nKL_length] at hm1, h1.symm⟩
    (by
      rintro p ⟨m, hm, rfl⟩ _ ⟨s, rfl⟩
      have hs : (s : ℕ) < 2 := lt_of_lt_of_eq s.2 u52n_KArr_size
      obtain ⟨m', hm', he⟩ := hcl m (by rwa [u52n_nKL_length]) s hs
      exact ⟨m', by rwa [u52n_nKL_length] at hm', he⟩)
    hc

theorem u52n_K_eq :
    (burnsideF48t_u52K' : Set (Equiv.Perm (Fin 462))) = ↑((Finset.range 9).image u52nκ) := by
  have hsub : (burnsideF48t_u52K' : Set (Equiv.Perm (Fin 462))) ⊆
      ↑((Finset.range 9).image u52nκ) := by
    intro c hc
    obtain ⟨m, hm, rfl⟩ := u52n_K_sub c hc
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, rfl⟩)
  have h9 : (burnsideF48t_u52K' : Set (Equiv.Perm (Fin 462))).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact burnsideF48t_u52_card_K'
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, h9]
  exact Finset.card_image_le.trans (by simp)

theorem u52n_κ_mem {m : ℕ} (hm : m < 9) :
    u52nκ m ∈ burnsideF48t_u52K' := by
  have : u52nκ m ∈ (burnsideF48t_u52K' : Set (Equiv.Perm (Fin 462))) := by
    rw [u52n_K_eq]
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, rfl⟩)
  exact this

theorem u52n_fixSet : fixSet burnsideF48t_u52K' = finOf 462 NF := by
  obtain ⟨-, -, hF⟩ := u52n_kfacts
  ext x
  rw [mem_fixSet, mem_finOf, hF x]
  constructor
  · intro H j hj
    apply H
    rw [u52n_K'_eq]
    exact Subgroup.subset_closure ⟨⟨j, by rw [u52n_KArr_size]; exact hj⟩, rfl⟩
  · intro H k hk
    rw [u52n_K'_eq] at hk
    have hle : Subgroup.closure (Set.range fun s : Fin (burnsideF48t_u52KArr ()).size =>
        u52nκ (burnsideF48t_u52KGenIdx.getD s 0)) ≤
        MulAction.stabilizer (Equiv.Perm (Fin 462)) x := by
      rw [Subgroup.closure_le]
      rintro _ ⟨s, rfl⟩
      have hs : (s : ℕ) < 2 := lt_of_lt_of_eq s.2 u52n_KArr_size
      exact MulAction.mem_stabilizer_iff.2 (H s hs)
    exact MulAction.mem_stabilizer_iff.1 (hle hk)

theorem u52n_red {H H' : Subgroup (Equiv.Perm (Fin 462))}
    {ok : ℕ → Bool} (hok : ∀ c, ok c = true → c < 4 ∧ burnsideF48t_u52σ c ∈ H)
    (hB : ∀ c < 2, burnsideF48t_u52σ c ∈ H')
    {nodes : List (List ℕ)} {par gen : List ℕ}
    (htree : treeOK 462 9 (mask 9) LP ok NF nodes par gen = true)
    {SV : List ℕ} {SW EW : List (List ℕ)}
    (hgens : gensOK 462 9 (mask 9) (pidn 462 9) LP ok SV SW = true)
    (hstab : stabOK 462 9 (mask 9) (pidn 462 9) NF SV EW = true)
    (hcard : Nat.card H = nodes.length * EW.length)
    (hpE : ∀ i < 36, ∀ c ∈ EW.getD i [], c < 3) (hpS : ∀ j < 3, ∀ c ∈ SW.getD j [], c < 2)
    {RW : List (List (Fin 4 × Bool))}
    (htest : ((elems 462 9 (mask 9) (pidn 462 9) SV EW).drop 36).all
      (cosetT 462 9 (mask 9) nKL (RW.map fun w =>
        evFK 462 9 (mask 9) (pidn 462 9) LP LPI (burnsideF48s_eInvW w))) = true)
    {x : Equiv.Perm (Fin 462)} (hx : x ∈ H) (hx' : x ∉ H')
    (hxK : ∀ k ∈ burnsideF48t_u52K', x * k * x⁻¹ ∈ burnsideF48t_u52K')
    (hxx : x * x ∈ burnsideF48t_u52K') :
    ∃ w ∈ RW, (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) w)⁻¹ * x ∈
      burnsideF48t_u52K' := by
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
  by_cases hi36 : i < 36
  · exfalso
    apply hx'
    rw [he_def]
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    have hc3 := hpE i hi36 c hc
    refine Subgroup.list_prod_mem _ fun z hz => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    exact hB l (hpS c hc3 l hl)
  · have hli : i < (elems 462 9 (mask 9) (pidn 462 9) SV EW).length := by
      simpa [elems] using hi
    have hmem : (elems 462 9 (mask 9) (pidn 462 9) SV EW).getD i 0 ∈
        (elems 462 9 (mask 9) (pidn 462 9) SV EW).drop 36 := by
      have h1 : i - 36 < ((elems 462 9 (mask 9) (pidn 462 9) SV EW).drop 36).length := by
        rw [List.length_drop]
        omega
      refine List.mem_iff_getElem.2 ⟨i - 36, h1, ?_⟩
      rw [List.getElem_drop, List.getD_eq_getElem _ _ hli]
      congr 1
      omega
    have hct := List.all_eq_true.1 htest _ hmem
    obtain ⟨hPE, hE0⟩ := hrep i hi
    simp only [cosetT, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at hct
    rcases hct with h1 | ⟨r, hr, h2⟩
    · exfalso
      obtain ⟨m, hm, hmeq⟩ := u52n_K_sub _ hxx
      have hkm : pcomp 462 9 (mask 9) ((elems 462 9 (mask 9) (pidn 462 9) SV EW).getD i 0)
          ((elems 462 9 (mask 9) (pidn 462 9) SV EW).getD i 0) = nKL.getD m 0 :=
        eq_of_prep (by norm_num) (CFSG.KS.PF.pcomp_shr _ _ (by norm_num) (by norm_num))
          (u52n_kl_shr hm) (Raw.Orb.prep_pcomp (by norm_num) hPE hPE)
          (by rw [hmeq]; exact u52n_klRep hm)
      have hin : memN (nKL.getD m 0) nKL = true := by
        rw [memN_iff, List.getD_eq_getElem _ _ (by rw [u52n_nKL_length]; exact hm)]
        exact List.getElem_mem _
      rw [hkm, hin] at h1
      exact absurd h1 (by decide)
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hr
      have hjRW : j < RW.length := by simpa using hj
      obtain ⟨m', hm', he⟩ := List.mem_iff_getElem.1 (memN_iff.1 h2)
      have hm9 : m' < 9 := by rwa [u52n_nKL_length] at hm'
      refine ⟨RW[j], List.getElem_mem _, ?_⟩
      have hrRep : Raw.Orb.PRep 462 9 ((RW.map fun w =>
          evFK 462 9 (mask 9) (pidn 462 9) LP LPI (burnsideF48s_eInvW w))[j])
          (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) RW[j])⁻¹ := by
        rw [List.getElem_map, ← burnsideF48s_e_ev_invW]
        exact u52n_evRep _
      have hprod := Raw.Orb.prep_pcomp (by norm_num) hrRep hPE
      have hk : u52nκ m' = (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) RW[j])⁻¹ *
          e i := by
        refine PRep.unique' (u52n_klRep hm9) ?_
        rw [List.getD_eq_getElem _ _ hm', he]
        exact hprod
      rw [← hk]
      exact u52n_κ_mem hm9

theorem u52n_take_all {EW : List (List ℕ)} {k b : ℕ}
    (h : ((EW.take k).all fun ew => ew.all fun c => Nat.blt c b) = true) :
    ∀ i < k, ∀ c ∈ EW.getD i [], c < b := by
  intro i hi c hc
  by_cases hiE : i < EW.length
  · rw [List.getD_eq_getElem _ _ hiE] at hc
    have hmem : EW[i] ∈ EW.take k := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
    have := List.all_eq_true.1 (List.all_eq_true.1 h _ hmem) c hc
    simpa [Nat.blt_eq] using this
  · rw [List.getD_eq_default _ _ (by omega)] at hc
    exact absurd hc List.not_mem_nil

theorem u52n_xred {x : Equiv.Perm (Fin 462)}
    (hx : x ∈ burnsideF48t_u52P1') (hx2 : x ∉ burnsideF48t_u52P2')
    (hxK : ∀ k ∈ burnsideF48t_u52K', x * k * x⁻¹ ∈ burnsideF48t_u52K')
    (hxx : x * x ∈ burnsideF48t_u52K') :
    ∃ w ∈ burnsideF48t_u52XW,
      (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) w)⁻¹ * x ∈ burnsideF48t_u52K' := by
  obtain ⟨-, hl1, -, -, hl2, -, -, hp1, -, hp2, -⟩ := nPref
  refine u52n_red (ok := okP1) (fun c hc => ?_) (fun c hc => u52n_σ_mem_P2 (Or.inl hc))
    nTreeP1 nGensP1 nStabP1 (by rw [burnsideF48t_u52_card_P1', hl1, hl2])
    (u52n_take_all hp1) (fun j hj c hc => ?_) nTestP1 hx hx2 hxK hxx
  · have hc3 : c < 3 := by simpa [okP1, Nat.blt_eq] using hc
    exact ⟨by omega, u52n_σ_mem_P1 hc3⟩
  · have := u52n_take_all (b := 2) (k := 3) (EW := SWP1) (by simpa [okB] using hp2) j hj c hc
    exact this

theorem u52n_yred {y : Equiv.Perm (Fin 462)}
    (hy : y ∈ burnsideF48t_u52P2') (hy1 : y ∉ burnsideF48t_u52P1')
    (hyK : ∀ k ∈ burnsideF48t_u52K', y * k * y⁻¹ ∈ burnsideF48t_u52K')
    (hyy : y * y ∈ burnsideF48t_u52K') :
    ∃ w ∈ burnsideF48t_u52YW,
      (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) w)⁻¹ * y ∈ burnsideF48t_u52K' := by
  obtain ⟨-, -, hl1, -, -, hl2, -, -, hp1, -, hp2⟩ := nPref
  refine u52n_red (ok := okP2) (fun c hc => ?_) (fun c hc => u52n_σ_mem_P1 (by omega))
    nTreeP2 nGensP2 nStabP2 (by rw [burnsideF48t_u52_card_P2', hl1, hl2])
    (u52n_take_all hp1) (fun j hj c hc => ?_) nTestP2 hy hy1 hyK hyy
  · have hc' : c < 2 ∨ c = 3 := by
      simp only [okP2, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
      exact hc
    exact ⟨by omega, u52n_σ_mem_P2 hc'⟩
  · have := u52n_take_all (b := 2) (k := 3) (EW := SWP2) (by simpa [okB] using hp2) j hj c hc
    exact this

end CertificateChecks.KernelU52

end
