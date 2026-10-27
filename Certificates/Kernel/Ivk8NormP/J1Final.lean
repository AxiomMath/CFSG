module

public import Certificates.Kernel.Ivk8NormP.J1
public import Certificates.Kernel.SporSch.J1.Cent2163B
public import CFSG.Certificates.Kernel.Ivk8NormPRes
public import CFSG.Certificates.Kernel.Ivk8NormSound
public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
public import CFSG.Certificates.Kernel.Spor.PK.CertBridge
public import CFSG.Certificates.SchreierChainOrder
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12NormP
public import CFSG.Sporadic.Schreier.J1Centralizer
public import CFSG.Sporadic.Schreier.J1Outer
import CFSG.Certificates.Kernel.Spor.RecGroup
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Norm
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

set_option maxRecDepth 400000

namespace CFSG.KS.Ivk8NormP.J1

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP CFSG.KC.Enum CFSG.KS
  CFSG.KS.SporSch.J1C CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J1
  CFSG.KS.Raw.Orb CFSG.Sporadic.Schreier CFSG.Certificates CFSG.KS.PK Subgroup

theorem ea_eq : ea = j1A1 :=
  CFSG.KS.RecGroup.perm_eq_of_rep rep_A rep_j1ATbl

theorem eb_eq : eb = j1A2 :=
  CFSG.KS.RecGroup.perm_eq_of_rep rep_B rep_j1BTbl

theorem aG_mem' (l : Int) : aG l ∈ j1P := by
  unfold aG
  split_ifs
  · rw [ea_eq]
    exact j1A1_mem
  · rw [ea_eq]
    exact inv_mem j1A1_mem
  · rw [eb_eq]
    exact j1A2_mem
  · rw [eb_eq]
    exact inv_mem j1A2_mem

@[expose] noncomputable def wG (w : List Int) : Equiv.Perm (Fin 3080) :=
  CFSG.Sporadic.Th.wordG aG w

theorem wG_nil : wG [] = 1 := by simp [wG, CFSG.Sporadic.Th.wordG]

theorem wG_cons (l : Int) (w : List Int) : wG (l :: w) = aG l * wG w := by
  simp [wG, CFSG.Sporadic.Th.wordG]

theorem wG_mem (w : List Int) : wG w ∈ j1P := by
  unfold wG CFSG.Sporadic.Th.wordG
  exact list_prod_mem fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact aG_mem' l

@[expose] def okL (w : List Int) : Bool := w.all fun l => l == 1 || l == -1 || l == 2 || l == -2

theorem okL_spec {w : List Int} (h : okL w = true) :
    ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  simpa [or_assoc] using this

theorem okL_invW {w : List Int} (h : okL w = true) : okL (invW w) = true := by
  unfold okL invW
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
  rcases okL_spec h a (List.mem_reverse.1 ha) with rfl | rfl | rfl | rfl <;> decide

theorem prep_evA {w : List Int} (h : okL w = true) : PRep 3080 12 (evA w) (wG w) :=
  prep_wordP w fun l hl => prep_ltrA (okL_spec h l hl)

theorem aG_neg {l : Int} (hl : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) : aG (-l) = (aG l)⁻¹ := by
  rcases hl with rfl | rfl | rfl | rfl <;> simp [aG]

theorem wG_invW : ∀ w : List Int, okL w = true → wG (invW w) = (wG w)⁻¹
  | [], _ => by simp [invW, wG_nil]
  | l :: w, h => by
    have h' : okL w = true := by
      simp only [okL, List.all_cons, Bool.and_eq_true] at h ⊢
      exact h.2
    have hl := okL_spec h l List.mem_cons_self
    have e : invW (l :: w) = invW w ++ [-l] := by simp [invW]
    have happ : ∀ u v : List Int, wG (u ++ v) = wG u * wG v := fun u v => by
      simp [wG, CFSG.Sporadic.Th.wordG]
    rw [e, happ, wG_invW w h', wG_cons, wG_cons, wG_nil, mul_one, aG_neg hl, mul_inv_rev]

theorem prep_evAi {w : List Int} (h : okL w = true) : PRep 3080 12 (evA (invW w)) (wG w)⁻¹ := by
  rw [← wG_invW w h]
  exact prep_evA (okL_invW h)

@[expose] noncomputable def gPs : List (Equiv.Perm (Fin 3080)) := j1Gw.map wG

theorem gPs_getD (i : ℕ) : gPs.getD i 1 = wG (j1Gw.getD i []) := by
  rw [← wG_nil, gPs, List.getD_map]

theorem okG (i : ℕ) : okL (j1Gw.getD i []) = true := by
  rcases i with _ | _ | _ | _ | i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem prep_gG (i : ℕ) : PRep 3080 12 (gG (i + 1)) (gPs.getD i 1) := by
  rw [gPs_getD]
  exact prep_evA (okG i)

theorem prep_gGI (i : ℕ) : PRep 3080 12 (gGI i) (gPs.getD i 1)⁻¹ := by
  rw [gPs_getD]
  exact prep_evAi (okG i)

theorem prep_evG : ∀ w : List Int, (∀ l ∈ w, l ≠ 0) →
    PRep 3080 12 (evG w) (evalCodes gPs w)
  | [], _ => by
    simpa [evG, wordP, evalCodes] using prep_pidn (n := 3080) (w := 12) (by norm_num)
      (by norm_num)
  | l :: w, h => by
    have ih := prep_evG w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hl : l ≠ 0 := h l List.mem_cons_self
    have hL : PRep 3080 12 (ltrK (fun k => gG (k + 1)) gGI l)
        (if 0 < l then gPs.getD (l.toNat - 1) 1 else (gPs.getD ((-l).toNat - 1) 1)⁻¹) := by
      rcases l with m | k
      · have hm : m ≠ 0 := fun h0 => hl (by rw [h0]; rfl)
        have hpos : (0 : ℤ) < Int.ofNat m := by
          rw [Int.ofNat_eq_natCast]
          omega
        rw [if_pos hpos]
        exact prep_gG (m - 1)
      · rw [if_neg (by omega)]
        exact prep_gGI k
    exact prep_pcomp n32 hL ih

theorem xw_ne : ∀ j, ∀ l ∈ j1Xw.getD j [], l ≠ 0 := by
  intro j l hl
  rcases j with _ | _ | _ | j
  · simp only [j1Xw, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hl
    omega
  · simp only [j1Xw, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
      or_false] at hl
    omega
  · simp only [j1Xw, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
      or_false] at hl
    omega
  · simp [j1Xw] at hl

theorem eq_of_beq {x y : ℕ} {g h : Equiv.Perm (Fin 3080)} (hx : PRep 3080 12 x g)
    (hy : PRep 3080 12 y h) (hb : Nat.beq x y = true) : g = h := by
  rw [Nat.eq_of_beq_eq_true hb] at hx
  exact prep_eq hx hy

@[expose] noncomputable def oN (i : ℕ) : ℕ := pg 12 (mask 12) j1O i

theorem oN_facts : ∀ i < 40, oN i < 3080 ∧ (i + 1 = 40 ∨ oN i < oN (i + 1)) := by
  have h := ch5253_j1_sorted
  unfold sortedOK at h
  rw [List.all_eq_true] at h
  intro i hi
  have := h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, beq_iff_eq] at this
  exact this

theorem oN_lt (i : Fin 40) : oN i < 3080 := (oN_facts i i.2).1

theorem oN_strictMono : StrictMono fun i : Fin 40 => oN i := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have hi := i.isLt
  rcases (oN_facts i (by omega)).2 with h | h
  · omega
  · simpa [Fin.val_succ] using h

@[expose] noncomputable def o : Fin 40 ↪ Fin 3080 :=
  ⟨fun i => ⟨oN i, oN_lt i⟩, fun a b h => oN_strictMono.injective (congrArg Fin.val h)⟩

theorem res_spec {X : ℕ} {g : Equiv.Perm (Fin 3080)} (hX : PRep 3080 12 X g) {σ : VP 40}
    (h : resOK 12 j1O 40 X σ = true) : ∀ i, g (o i) = o (pkp σ i) := by
  intro i
  unfold resOK at h
  rw [List.all_eq_true] at h
  have e := Nat.eq_of_beq_eq_true (h i (List.mem_range.2 i.2))
  apply Fin.ext
  have e1 := hX ⟨oN i, oN_lt i⟩
  change (g ⟨oN i, oN_lt i⟩ : ℕ) = oN (pkp σ i)
  rw [← e1, pkp_apply]
  exact e

@[expose] noncomputable def ρ (g : Equiv.Perm (Fin 3080)) : Equiv.Perm (Fin 40) := by
  classical
  exact if h : g ∈ resStab o then resHom o ⟨g, h⟩ else 1

theorem resHom_eq_ρ {g : Equiv.Perm (Fin 3080)} (hg : g ∈ resStab o) :
    resHom o ⟨g, hg⟩ = ρ g := by
  rw [ρ, dif_pos hg]

theorem ρ_mul {g h : Equiv.Perm (Fin 3080)} (hg : g ∈ resStab o) (hh : h ∈ resStab o) :
    ρ (g * h) = ρ g * ρ h := by
  rw [← resHom_eq_ρ hg, ← resHom_eq_ρ hh, ← resHom_eq_ρ (mul_mem hg hh)]
  exact (resHom o).map_mul ⟨g, hg⟩ ⟨h, hh⟩

theorem ρ_inv {g : Equiv.Perm (Fin 3080)} (hg : g ∈ resStab o) : ρ g⁻¹ = (ρ g)⁻¹ := by
  rw [← resHom_eq_ρ hg, ← resHom_eq_ρ (inv_mem hg)]
  exact (resHom o).map_inv ⟨g, hg⟩

theorem ρ_one : ρ 1 = 1 := by
  rw [← resHom_eq_ρ (one_mem _)]
  exact (resHom o).map_one

theorem res_of {X : ℕ} {g : Equiv.Perm (Fin 3080)} (hX : PRep 3080 12 X g) {σ : VP 40}
    (h : resOK 12 j1O 40 X σ = true) : g ∈ resStab o ∧ ρ g = pkp σ := by
  have hm := mem_resStab_of (res_spec hX h)
  exact ⟨hm, by rw [← resHom_eq_ρ hm, resHom_eq hm (res_spec hX h)]⟩

theorem j1Sig_length : j1Sig.length = 4 := rfl

theorem j1Fr1_length : j1Fr1.length = 3 := rfl

theorem j1Fr2_length : j1Fr2.length = 3 := rfl

theorem prep_z : PRep 3080 12 zN j1A1 := by
  have h := prep_evA (w := [1]) rfl
  rwa [wG_cons, wG_nil, mul_one, aG, if_pos rfl, ea_eq] at h

theorem res_gen (i : ℕ) :
    gPs.getD i 1 * j1A1 = j1A1 * gPs.getD i 1 ∧ gPs.getD i 1 ∈ j1P ∧
      gPs.getD i 1 ∈ resStab o ∧ ρ (gPs.getD i 1) = (j1Sig.map pkp).getD i 1 := by
  have hmem : gPs.getD i 1 ∈ j1P := by
    rw [gPs_getD]
    exact wG_mem _
  by_cases hi : i < 4
  · have hr := List.all_eq_true.1 ch5253_j1_res i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at hr
    obtain ⟨hc, hres⟩ := hr
    obtain ⟨hm, hρ⟩ := res_of (prep_gG i) hres
    refine ⟨eq_of_beq (prep_pcomp n32 (prep_gG i) prep_z) (prep_pcomp n32 prep_z (prep_gG i)) hc,
      hmem, hm, ?_⟩
    rw [hρ, ← pkp_oneV, List.getD_map]
  · have h1 : gPs.getD i 1 = 1 := List.getD_eq_default _ _ (by simp [gPs, j1Gw]; omega)
    have h2 : (j1Sig.map pkp).getD i 1 = 1 :=
      List.getD_eq_default _ _ (by rw [List.length_map, j1Sig_length]; omega)
    rw [h1, h2, ρ_one]
    exact ⟨by group, one_mem _, one_mem _, rfl⟩

theorem res_word {K : Subgroup (Equiv.Perm (Fin 3080))}
    (hK : K ≤ resStab o) (hG : ∀ i, gPs.getD i 1 ∈ K) :
    ∀ w, evalCodes gPs w ∈ K ∧ ρ (evalCodes gPs w) = evalCodes (j1Sig.map pkp) w
  | [] => ⟨one_mem _, ρ_one⟩
  | z :: w => by
    obtain ⟨hw, hρw⟩ := res_word hK hG w
    rw [evalCodes, evalCodes]
    split_ifs
    · refine ⟨mul_mem (hG _) hw, ?_⟩
      rw [ρ_mul (res_gen _).2.2.1 (hK hw), (res_gen _).2.2.2, hρw]
    · refine ⟨mul_mem (inv_mem (hG _)) hw, ?_⟩
      rw [ρ_mul (inv_mem (res_gen _).2.2.1) (hK hw), ρ_inv (res_gen _).2.2.1, (res_gen _).2.2.2,
        hρw]

theorem prime_dvd_120 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 120) : p = 3 ∨ p = 5 := by
  have e : (120 : ℕ) = 2 ^ 3 * (3 * 5) := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)

theorem ordV_certificate_base' {n : ℕ} (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List ℤ)) {k : ℕ} (base : Vector (Fin n) k) (hbase : base.toList.Nodup)
    (Sc : List (VP n)) : ordV Sc (certificate hn gens words base hbase).base = ordV Sc base := rfl

@[expose] noncomputable def Q : CFSG.Certificates.RawSchreierDatum 40 :=
  certificate (by decide) (j1Sig.map pkp) [] #v[0, 2] (by decide)

theorem Q_strong : Q.strong.toList = j1Strong.map pkp :=
  certificate_strong_eq (by decide) _ [] #v[0, 2] (by decide) j1Strong rfl

theorem Q_valid : Q.check = true :=
  check_of_schV (by decide) _ [] #v[0, 2] (by decide) j1Strong Q_strong ch5253_j1_sch

theorem Q_card : Nat.card Q.originalSubgroup = 120 := by
  rw [← Q.orderCertificate_eq_card Q_valid, orderCertificate_eq_ordV Q j1Strong Q_strong]
  unfold Q
  rw [ordV_certificate_base', Nat.eq_of_beq_eq_true ch5253_j1_ord]

theorem Q_mem (g : Equiv.Perm (Fin 40)) :
    g ∈ Q.originalSubgroup ↔ g ∈ (enumV j1Strong #v[0, 2]).map pkp := by
  rw [← mem_enumeration_iff Q Q_valid, enumeration_eq_enumV Q j1Strong Q_strong]
  rfl

theorem j1_noP
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ P W : Subgroup (Equiv.Perm (Fin 3080)), P ≤ j1P → W ≤ j1P → Nat.card P = 2 ^ 3 →
      IsPGroup p W → P ≤ normalizer (W : Set (Equiv.Perm (Fin 3080))) → W = ⊥ := by
  classical
  set T := j1A1 with hT
  have ht2 : orderOf T = 2 := at_j1_image_pair_count.1
  have hTT : T * T = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hT1 : T ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hCc : Nat.card (centralizerIn j1P T) = 120 :=
    (j1P_involution_centralizer T j1A1_mem ht2).1
  set K := closure (Set.range fun i => gPs.getD i 1) with hKdef
  have hG : ∀ i, gPs.getD i 1 ∈ K := fun i => subset_closure ⟨i, rfl⟩
  have hKS : K ≤ resStab o := by
    rw [hKdef, closure_le]
    rintro _ ⟨i, rfl⟩
    exact (res_gen i).2.2.1
  have hKC : K ≤ centralizerIn j1P T := by
    rw [hKdef, closure_le]
    rintro _ ⟨i, rfl⟩
    exact mem_centralizerIn.2 ⟨(res_gen i).2.1, (res_gen i).1⟩
  have hKP : K ≤ j1P := fun x hx => (mem_centralizerIn.1 (hKC hx)).1
  have hw := res_word hKS hG
  have hL : ∀ l ∈ Q.originalSubgroup, ∃ x, ∃ hx : x ∈ K, resHom o ⟨x, hKS hx⟩ = l := by
    have hle : Q.originalSubgroup ≤ (K.subgroupOf (resStab o)).map (resHom o) := by
      unfold Q
      rw [certificate_originalSubgroup, closure_le]
      rintro _ hz
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
      refine ⟨⟨_, hKS (hG k)⟩, hG k, ?_⟩
      rw [resHom_eq_ρ, (res_gen k).2.2.2, ← pkp_oneV, List.getD_map, List.getD_eq_getElem _ _ hk]
    intro l hl
    obtain ⟨⟨x, hxS⟩, hxK, rfl⟩ := hle hl
    exact ⟨x, hxK, rfl⟩
  have hKge : Nat.card Q.originalSubgroup ≤ Nat.card K := by
    let φ : K →* Equiv.Perm (Fin 40) := (resHom o).comp (Subgroup.inclusion hKS)
    have hQr : Q.originalSubgroup ≤ φ.range := by
      intro l hl
      obtain ⟨x, hx, rfl⟩ := hL l hl
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (Subgroup.card_le_of_le hQr).trans
      (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective)
  have hKeq : K = centralizerIn j1P T :=
    Subgroup.eq_of_le_of_card_ge hKC (by rw [hCc, ← Q_card]; exact hKge)
  have hKc : Nat.card K = 120 := by rw [hKeq, hCc]
  obtain ⟨hρK, hinj⟩ := res_injOn hKS hL (by rw [hKc, Q_card])
  have hinj' : ∀ x ∈ K, ∀ y ∈ K, ρ x = ρ y → x = y := fun x hx y hy h =>
    hinj x hx y hy (by rw [resHom_eq_ρ, resHom_eq_ρ]; exact h)
  have hLL : ∀ y (hy : y ∈ K), ∃ y' ∈ enumV j1Strong #v[0, 2],
      resHom o ⟨y, hKS hy⟩ = pkp y' := by
    intro y hy
    obtain ⟨y', hy', e⟩ := List.mem_map.1 ((Q_mem _).1 (hρK y hy))
    exact ⟨y', hy', e.symm⟩
  set Xs := j1Xw.map (evalCodes gPs) with hXs
  set S : Set (Equiv.Perm (Fin 3080)) := {x | x ∈ Xs} with hS
  have hXK : ∀ x ∈ Xs, x ∈ K ∧ ρ x ∈ j1Xs.map pkp := by
    intro x hx
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hx
    refine ⟨(hw w).1, ?_⟩
    rw [(hw w).2, ← pkp_evV]
    exact List.mem_map_of_mem (List.mem_map_of_mem hw')
  have hxs := ch5253_j1_xs
  simp only [Bool.and_eq_true, List.all_eq_true] at hxs
  have hinvS : ∀ x ∈ S, x * x = 1 := by
    intro x hx
    obtain ⟨hxK, hρx⟩ := hXK x hx
    refine hinj' _ (mul_mem hxK hxK) _ (one_mem _) ?_
    rw [ρ_mul (hKS hxK) (hKS hxK), ρ_one]
    obtain ⟨u, hu, e⟩ := List.mem_map.1 hρx
    have := eq_of_not_difV (hxs.1 u hu : (!difV (mulV u u) (oneV 40)) = true)
    rw [pkp_mulV, pkp_oneV, e] at this
    exact this
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxK, hρx⟩ := hXK x hx
    obtain ⟨hyK, hρy⟩ := hXK y hy
    refine hinj' _ (mul_mem hxK hyK) _ (mul_mem hyK hxK) ?_
    rw [ρ_mul (hKS hxK) (hKS hyK), ρ_mul (hKS hyK) (hKS hxK)]
    obtain ⟨u, hu, e⟩ := List.mem_map.1 hρx
    obtain ⟨v, hv, e'⟩ := List.mem_map.1 hρy
    have := eq_of_not_difV (hxs.2 u hu v hv : (!difV (mulV u v) (mulV v u)) = true)
    rw [pkp_mulV, pkp_mulV, e, e'] at this
    exact this
  have hXS : ∀ j < 3, evalCodes gPs (j1Xw.getD j []) ∈ S := by
    intro j hj
    refine List.mem_map_of_mem ?_
    rw [List.getD_eq_getElem _ _ (by simpa [j1Xw] using hj)]
    exact List.getElem_mem _
  have hXmem : ∀ j < 3, evalCodes gPs (j1Xw.getD j []) ∈ closure S := fun j hj =>
    subset_closure (hXS j hj)
  have hX₁ : evalCodes gPs (j1Xw.getD 0 []) = T := by
    have e : evalCodes gPs (j1Xw.getD 0 []) = (gPs.getD 0 1)⁻¹ := by
      simp [j1Xw, evalCodes]
    have e0 : gPs.getD 0 1 = T := by
      rw [gPs_getD]
      simp [j1Gw, wG_cons, wG_nil, aG, ea_eq, hT]
    rw [e, e0]
    exact inv_eq_of_mul_eq_one_right hTT
  have hTS : T ∈ closure S := by
    rw [← hX₁]
    exact hXmem 0 (by norm_num)
  set X₂ := evalCodes gPs (j1Xw.getD 1 []) with hX₂
  have hX₂S : X₂ ∈ closure S := hXmem 1 (by norm_num)
  set C₁ := wG j1C1w with hC₁
  set C₂ := wG j1C2w with hC₂
  have hok1 : okL j1C1w = true := rfl
  have hok2 : okL j1C2w = true := rfl
  have hconj := ch5253_j1_conj
  simp only [Bool.and_eq_true, List.all_eq_true] at hconj
  obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hconj
  have hGw : ∀ j, PRep 3080 12 (evG (j1Xw.getD j [])) (evalCodes gPs (j1Xw.getD j [])) :=
    fun j => prep_evG _ (xw_ne j)
  have hc1' : C₁ * T = X₂ * C₁ :=
    eq_of_beq (prep_pcomp n32 (prep_evA hok1) prep_z) (prep_pcomp n32 (hGw 1) (prep_evA hok1)) hc1
  have hc2' : C₂ * T = T * X₂ * C₂ :=
    eq_of_beq (prep_pcomp n32 (prep_evA hok2) prep_z)
      (prep_pcomp n32 (prep_pcomp n32 prep_z (hGw 1)) (prep_evA hok2)) hc2
  have hfr : ∀ {cw : List Int}, okL cw = true → ∀ {X : ℕ} {g : Equiv.Perm (Fin 3080)},
      PRep 3080 12 X g → PRep 3080 12 (frN cw X) ((wG cw)⁻¹ * g * wG cw) := by
    intro cw hcw X g hX
    have := prep_pcomp n32 (prep_evAi hcw) (prep_pcomp n32 hX (prep_evA hcw))
    rwa [← mul_assoc] at this
  have hF0 : ∀ f ∈ j1Xs, ∃ x ∈ closure S, ∃ hx : (1 : Equiv.Perm (Fin 3080))⁻¹ * x * 1 ∈ resStab o,
      resHom o ⟨_, hx⟩ = pkp f := by
    intro f hf
    obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hf
    have e : (1 : Equiv.Perm (Fin 3080))⁻¹ * evalCodes gPs w * 1 = evalCodes gPs w := by group
    refine ⟨evalCodes gPs w, subset_closure (List.mem_map_of_mem hw'), e ▸ hKS (hw w).1, ?_⟩
    rw [resHom_eq_ρ, e, (hw w).2, pkp_evV]
  have hF : ∀ {cw : List Int} {F : List (VP 40)}, okL cw = true → F.length = 3 →
      (∀ j < 3, resOK 12 j1O 40 (frN cw (evG (j1Xw.getD j []))) (F.getD j (oneV 40)) = true) →
      ∀ f ∈ F, ∃ x ∈ closure S, ∃ hx : (wG cw)⁻¹ * x * wG cw ∈ resStab o,
        resHom o ⟨_, hx⟩ = pkp f := by
    intro cw F hcw hlen hres f hf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    have hj3 : j < 3 := by rwa [hlen] at hj
    have hr := hres j hj3
    rw [List.getD_eq_getElem _ _ hj] at hr
    obtain ⟨hm, hρ⟩ := res_of (hfr hcw (hGw j)) hr
    exact ⟨_, hXmem j hj3, hm, by rw [resHom_eq_ρ, hρ]⟩
  have hF1 := hF (F := j1Fr1) hok1 j1Fr1_length fun j hj => (hc3 j (List.mem_range.2 hj)).1
  have hF2 := hF (F := j1Fr2) hok2 j1Fr2_length fun j hj => (hc3 j (List.mem_range.2 hj)).2
  have hw40 := ch5253_j1_w
  simp only [j1W, Bool.and_eq_true] at hw40
  obtain ⟨⟨⟨⟨⟨w1, w2⟩, w3⟩, w4⟩, w5⟩, w6⟩ := hw40
  have hwd : wd 40 = 6 := by decide
  have hN : ∀ y ∈ K, ∀ c ∈ [1, C₁, C₂], orderOf y = p →
      ∃ h ∈ closure S, h ∉ normalizer (zpowers (c * y * c⁻¹) : Set (Equiv.Perm (Fin 3080))) := by
    intro y hy c hc hyo
    have hp35 : p = 3 ∨ p = 5 := by
      refine prime_dvd_120 hp hp2 ?_
      rw [← hKc, ← hyo, ← Subgroup.orderOf_mk y hy]
      exact _root_.orderOf_dvd_natCard _
    have key : ∀ (c : Equiv.Perm (Fin 3080)) (F : List (VP 40)),
        (∀ f ∈ F, ∃ x ∈ closure S, ∃ hx : c⁻¹ * x * c ∈ resStab o, resHom o ⟨_, hx⟩ = pkp f) →
        chkP 40 6 p (wits F) j1Enum = true →
        ∃ h ∈ closure S, h ∉ normalizer (zpowers (c * y * c⁻¹) : Set (Equiv.Perm (Fin 3080))) := by
      intro c F hF' hck
      rw [← hwd] at hck
      exact hN_of_res (by norm_num) (by rw [hwd]; norm_num) hp hKS hinj c hF' hLL hck y hy hyo
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    have hF0' : ∀ f ∈ j1Xs, ∃ x ∈ closure S, ∃ hx : (1 : Equiv.Perm (Fin 3080))⁻¹ * x * 1 ∈
        resStab o, resHom o ⟨_, hx⟩ = pkp f := hF0
    rcases hp35 with rfl | rfl <;> rcases hc with rfl | rfl | rfl
    · exact key _ _ hF0' w1
    · exact key _ _ hF1 w3
    · exact key _ _ hF2 w5
    · exact key _ _ hF0' w2
    · exact key _ _ hF1 w4
    · exact key _ _ hF2 w6
  have hBB : X₂ * X₂ = 1 := hinvS X₂ (hXS 1 (by norm_num))
  have hAB : T * X₂ = X₂ * T := by
    rw [← hX₁]
    exact hcommS _ (hXS 0 (by norm_num)) _ (hXS 1 (by norm_num))
  have hX₂c : C₁ * T * C₁⁻¹ = X₂ := by rw [hc1', mul_inv_cancel_right]
  have hTX₂c : C₂ * T * C₂⁻¹ = T * X₂ := by rw [hc2', mul_inv_cancel_right]
  have hB1 : X₂ ≠ 1 := by
    intro h
    apply hT1
    have : C₁ * T * C₁⁻¹ = 1 := hX₂c.trans h
    calc T = C₁⁻¹ * (C₁ * T * C₁⁻¹) * C₁ := by group
      _ = 1 := by rw [this]; group
  have hAneB : T ≠ X₂ := by
    intro h
    apply hT1
    have h1 : C₂ * T * C₂⁻¹ = 1 := by rw [hTX₂c, ← h, hTT]
    calc T = C₂⁻¹ * (C₂ * T * C₂⁻¹) * C₂ := by group
      _ = 1 := by rw [h1]; group
  have hcov : ∀ e ∈ [T, X₂, T * X₂], ∃ c ∈ [1, C₁, C₂], c * T * c⁻¹ = e := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨1, by simp, by group⟩
    · exact ⟨C₁, by simp, hX₂c⟩
    · exact ⟨C₂, by simp, hTX₂c⟩
  have hcs : ∀ c ∈ [1, C₁, C₂], c ∈ j1P := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact one_mem _
    · exact wG_mem _
    · exact wG_mem _
  have hHS : closure S ≤ j1P := by
    rw [closure_le]
    intro x hx
    exact hKP (hXK x hx).1
  have hHc : ∀ h ∈ closure S, h * T = T * h ∧ h * X₂ = X₂ * h := fun h hh =>
    ⟨comm_of_mem_closure hcommS h hh _ hTS, comm_of_mem_closure hcommS h hh _ hX₂S⟩
  have hKmem : ∀ x ∈ j1P, x * T = T * x → x ∈ K := by
    intro x hx hxr
    rw [hKeq]
    exact mem_centralizerIn.2 ⟨hx, hxr⟩
  have hpK : ¬ p ^ 2 ∣ Nat.card K := by
    rw [hKc]
    intro h
    rcases prime_dvd_120 hp hp2 ((dvd_pow_self p two_ne_zero).trans h) with rfl | rfl <;>
      norm_num at h
  have hS₀ : ¬ 2 ^ (3 + 1) ∣ Nat.card j1P := by
    rw [card_j1P]
    norm_num
  exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.noP_of_cent le_rfl hp hp2 hTS hX₂S hTT hBB hAB hT1
    hB1 hAneB (isPGroup_two_closure hinvS hcommS) hHS hHc hKmem hpK hcs hcov hN hS₀

end CFSG.KS.Ivk8NormP.J1

end
