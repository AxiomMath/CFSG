
module

public import Certificates.Kernel.He7223.Glue
public import Certificates.Kernel.He7223.Cent
public import CFSG.Sporadic.HeldB.InnerClass

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelHe7223.C1S CFSG.Quasithin.KGC31.He.c1W
#kss_strof CertificateChecks.KernelHe7223.SGS CFSG.Quasithin.KGC31.He.sigmaW
#kss_strof CertificateChecks.KernelHe7223.T1S CFSG.Quasithin.KGC31.He.t1W

namespace CertificateChecks.KernelHe7223

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.WordPts CFSG.KC.OrbPath
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CertificateChecks.KernelLC.HeFix
  CertificateChecks.KernelSchreierFam.He725

theorem inv_mul_mem_heP
    {x y : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup) (hy : y ∈ heAutGroup) (hxP : x ∉ heP)
    (hyP : y ∉ heP) : y⁻¹ * x ∈ heP := by
  rcases mem_heAutGroup_cases hx with h | h
  · exact absurd h hxP
  rcases mem_heAutGroup_cases hy with h' | h'
  · exact absurd h' hyP
  have e : y⁻¹ * x = heAutU * ((y * heAutU)⁻¹ * (x * heAutU)) * heAutU⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp heAutU_mem_normalizer _).mp
    (heP.mul_mem (heP.inv_mem h') h)

theorem card_CR_le :
    Nat.card (centralizerIn heAutGroup heT1P) ≤ 43008 := by
  classical
  by_cases hy : ∃ y ∈ centralizerIn heAutGroup heT1P, y ∉ heP
  · obtain ⟨y, hyC, hyP⟩ := hy
    have hyC' := mem_centralizerIn.1 hyC
    have hcomm : ∀ x : centralizerIn heAutGroup heT1P,
        y⁻¹ * (x : Equiv.Perm (Fin 8330)) * heT1P = heT1P * (y⁻¹ * x) := fun x => by
      have h1 := (mem_centralizerIn.1 x.2).2
      have h2 : y⁻¹ * heT1P = heT1P * y⁻¹ := by
        calc y⁻¹ * heT1P = y⁻¹ * (heT1P * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * heT1P) * y⁻¹ := by rw [hyC'.2]
          _ = heT1P * y⁻¹ := by group
      calc y⁻¹ * (x : Equiv.Perm (Fin 8330)) * heT1P = y⁻¹ * (x * heT1P) := by group
        _ = y⁻¹ * (heT1P * x) := by rw [h1]
        _ = (y⁻¹ * heT1P) * x := by group
        _ = (heT1P * y⁻¹) * x := by rw [h2]
        _ = heT1P * (y⁻¹ * x) := by group
    let f : centralizerIn heAutGroup heT1P → Bool × centralizerIn heP heT1P := fun x =>
      if hx : (x : Equiv.Perm (Fin 8330)) ∈ heP then
        (false, ⟨x, mem_centralizerIn.2 ⟨hx, (mem_centralizerIn.1 x.2).2⟩⟩)
      else (true, ⟨y⁻¹ * x, mem_centralizerIn.2
        ⟨inv_mul_mem_heP (mem_centralizerIn.1 x.2).1 hyC'.1 hx hyP, hcomm x⟩⟩)
    have hf : Function.Injective f := by
      intro a b hab
      dsimp only [f] at hab
      rcases em ((a : Equiv.Perm (Fin 8330)) ∈ heP) with ha | ha <;>
        rcases em ((b : Equiv.Perm (Fin 8330)) ∈ heP) with hb | hb
      · rw [dif_pos ha, dif_pos hb] at hab
        have h2 : (a : Equiv.Perm (Fin 8330)) = (b : Equiv.Perm (Fin 8330)) :=
          Subtype.mk.inj (Prod.mk.inj hab).2
        exact Subtype.ext h2
      · rw [dif_pos ha, dif_neg hb] at hab
        exact absurd (Prod.mk.inj hab).1 (by decide)
      · rw [dif_neg ha, dif_pos hb] at hab
        exact absurd (Prod.mk.inj hab).1 (by decide)
      · rw [dif_neg ha, dif_neg hb] at hab
        have h2 : y⁻¹ * (a : Equiv.Perm (Fin 8330)) = y⁻¹ * b :=
          Subtype.mk.inj (Prod.mk.inj hab).2
        exact Subtype.ext (mul_left_cancel h2)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, card_heP_cent1, Nat.card_eq_fintype_card (α := Bool),
      Fintype.card_bool] at this
    omega
  · push Not at hy
    have hle : centralizerIn heAutGroup heT1P ≤ centralizerIn heP heT1P := fun x hx =>
      mem_centralizerIn.2 ⟨hy x hx, (mem_centralizerIn.1 hx).2⟩
    have := Subgroup.card_le_of_le hle
    rw [card_heP_cent1] at this
    omega

theorem eSub_le_of {k : ℕ} {v : Fin k → Equiv.Perm (Fin 8330)} (hv : EBasis v)
    {H : Subgroup (Equiv.Perm (Fin 8330))} (hvH : ∀ i, v i ∈ H) : eSub hv ≤ H := by
  rw [eSub_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact hvH i

theorem mem_eSub_of_orbit
    {k N : ℕ} {v : Fin k → Equiv.Perm (Fin 8330)} (hv : EBasis v) (hvP : ∀ i, v i ∈ heP)
    (i₀ : Fin k) (hv0 : v i₀ = heT1P) {T : List (Equiv.Perm (Fin 8330))}
    (hT : ∀ t ∈ T, t ∈ eSub hv) (c : ℕ → Equiv.Perm (Fin 8330))
    (hc : ∀ j < N, c j ∈ centralizerIn heAutGroup heT1P)
    (hinj : ∀ j < N, ∀ j' < N, (∀ t ∈ T, c j * t * (c j)⁻¹ = c j' * t * (c j')⁻¹) → j = j')
    (hN : 43008 ≤ N * 2 ^ k) {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hx1 : x * heT1P = heT1P * x) (hxT : ∀ t ∈ T, x * t = t * x) : x ∈ eSub hv := by
  have hES : eSub hv ≤ centralizerIn heAutGroup heT1P ⊓ Subgroup.centralizer {y | y ∈ T} :=
    fun y hy => by
      refine Subgroup.mem_inf.2 ⟨mem_centralizerIn.2
        ⟨heP_le_heAutGroup (eSub_le_of hv hvP hy), ?_⟩, ?_⟩
      · rw [← hv0]
        exact eSub_comm hv _ _ hy (mem_eSub hv i₀)
      · rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact eSub_comm hv _ _ (hT t ht) hy
  have h1 := card_inf_centralizer_mul_le _ T c hc hinj
  have h2 := card_CR_le
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp at hN
  have h3 : Nat.card ↥(centralizerIn heAutGroup heT1P ⊓ Subgroup.centralizer {y | y ∈ T}) ≤
      Nat.card (eSub hv) := by
    rw [card_eSub]
    refine Nat.le_of_mul_le_mul_left ?_ hNpos
    rw [mul_comm]
    exact h1.trans (h2.trans hN)
  have heq := Subgroup.eq_of_le_of_card_ge hES h3
  have hxS : x ∈ centralizerIn heAutGroup heT1P ⊓ Subgroup.centralizer {y | y ∈ T} :=
    Subgroup.mem_inf.2 ⟨mem_centralizerIn.2 ⟨hx, hx1⟩,
      Subgroup.mem_centralizer_iff.2 fun t ht => (hxT t ht).symm⟩
  rw [← heq] at hxS
  exact hxS

theorem decodeW_ofList (cs : List Char) :
    decodeW (String.ofList cs) = (cs.filter (· ≠ '0')).map decodeL := by
  simp [decodeW]

theorem t1W_eq : t1W = gw 8 := by
  rw [T1S.eq, decodeW_ofList]
  decide +kernel

theorem sigmaW_eq : sigmaW = gw 7 := by
  rw [SGS.eq, decodeW_ofList]
  decide +kernel

theorem c1W_eq : c1W.getD 5 [] = gw 9 ∧ c1W.getD 10 [] = gw 10 := by
  rw [C1S.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel))]
  decide +kernel

theorem elt_t1W :
    elt t1W = heT1P := (rep_wA (by decide)).unique rep_t1A

@[expose] noncomputable def hsL : List (Equiv.Perm (Fin 8330)) := [elt (gw 9), elt (gw 10), elt (gw 7)]

theorem GW_letters : ∀ j < 11, lettersOK 3 (gw j) = true := by decide +kernel

theorem rep_HC {j : ℕ} (hj : j < 3) :
    Rep 8330 (unpack 8330 14 (HC j)) (hsL.getD j 1) := by
  have key : ∀ {i : ℕ} {r : ℕ}, i < 11 →
      wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (gw i) r = true →
      Rep 8330 (unpack 8330 14 r) (elt (gw i)) := fun {i} {r} hi h => by
    rw [← (wordEqK_sound gA_bind kPLU h).1]
    exact rep_wA (GW_letters _ hi)
  match j, hj with
  | 0, _ => exact key (by norm_num) ch7223kH5
  | 1, _ => exact key (by norm_num) ch7223kH10
  | 2, _ => exact key (by norm_num) ch7223kHS

theorem letRep_HC :
    LetRep 8330 14 HC HCI hsL := by
  intro j hj
  have hj3 : j < 3 := hj
  have hrep := rep_HC hj3
  have hp : permOK 8330 14 (mask 14) (8330 * 14) (HC j) (HCI j) = true := allN_ct ch7223kHI j hj3
  obtain ⟨h1, h2⟩ := rep_permOfArr (Orb.isInvA_unpack hp)
  have e := h1.unique hrep
  rw [e] at h2
  exact ⟨Orb.prep_of_rep hrep, Orb.prep_of_rep h2⟩

theorem gw_mem {j : ℕ} (hj : j < 11) : ∀ wd ∈ [gw j], lettersOK gens3.length wd = true := by
  intro wd hw
  rw [List.mem_singleton] at hw
  subst hw
  exact GW_letters j hj

theorem hs_mem_CR :
    ∀ g ∈ hsL, g ∈ centralizerIn heAutGroup heT1P := by
  have andB_true : ∀ {a b : Bool}, CFSG.KLie.CT.andB a b = true → a = true ∧ b = true := by
    intro a b h
    cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)
  obtain ⟨h7, h910⟩ := andB_true ch7223tc
  obtain ⟨h9, h10⟩ := andB_true h910
  have key : ∀ {i : ℕ}, i < 11 → conjPtsK 8330 14 LU LUI bsL (gw i) (gw 8) [gw 8] = true →
      elt (gw i) ∈ centralizerIn heAutGroup heT1P := fun {i} hi h => by
    have h8 : elt (gw 8) = heT1P := by rw [← t1W_eq]; exact elt_t1W
    have hpt := conjPtsK_sound letRep_LU (GW_letters _ hi) (GW_letters 8 (by norm_num))
      (gw_mem (j := 8) (by norm_num)) h
    have hmem : elt (gw i) * heT1P * (elt (gw i))⁻¹ ∈ heP :=
      (Subgroup.mem_normalizer_iff.mp (heAutGroup_le_normalizer (elt_mem_heAutGroup _)) _).mp
        heT1P_mem
    have he := eq_of_pts (bsL_eq ▸ baseFaithful_heP) hmem heT1P_mem fun p hp => by
      have := hpt p hp
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
      change (elt (gw i) * elt (gw 8) * (elt (gw i))⁻¹) p = elt (gw 8) p at this
      rwa [h8] at this
    refine mem_centralizerIn.2 ⟨elt_mem_heAutGroup _, ?_⟩
    calc elt (gw i) * heT1P = (elt (gw i) * heT1P * (elt (gw i))⁻¹) * elt (gw i) := by group
      _ = heT1P * elt (gw i) := by rw [he]
  intro g hg
  simp only [hsL, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact key (by norm_num) h9
  · exact key (by norm_num) h10
  · exact key (by norm_num) h7

theorem closure_hs_le :
    Subgroup.closure {x | x ∈ hsL} ≤ centralizerIn heAutGroup heT1P :=
  (Subgroup.closure_le _).2 fun g hg => hs_mem_CR g hg

theorem EB0 : EB.getD 0 [] = gw 8 := by decide +kernel

theorem QB0 : QB.getD 0 [] = gw 8 := by decide +kernel

theorem T5_letters : ∀ t ∈ T5, lettersOK 3 t = true := by decide +kernel

theorem T7_letters : ∀ t ∈ T7, lettersOK 3 t = true := by decide +kernel

theorem cent_E
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hxc : ∀ i : Fin 4, x * elt (eW.getD i []) = elt (eW.getD i []) * x) :
    x ∈ eSub ebasis_E := by
  have hget : ∀ i, eW.getD i [] = EB.getD i [] := fun i => by rw [eW_eq]
  obtain ⟨c, hc, hinj⟩ := orbRecK_sound (by norm_num) letRep_LU rfl letRep_HC (by norm_num)
    (fun t ht => T5_letters t ht) ch7223o5
  have hmem : ∀ j : ℕ, (hj : j < 6) → elt (EB.getD j []) ∈ eSub ebasis_E := fun j hj => by
    rw [← hget j]
    exact mem_eSub ebasis_E ⟨j, hj⟩
  have hcom : ∀ j : ℕ, (hj : j < 4) → x * elt (EB.getD j []) = elt (EB.getD j []) * x :=
    fun j hj => by
      rw [← hget j]
      exact hxc ⟨j, hj⟩
  refine mem_eSub_of_orbit ebasis_E (fun i => by
      change elt (eW.getD i []) ∈ heP
      rw [hget i]
      exact elt_mem_heP (EB_letters _ (getD_mem (lt_of_lt_of_eq i.2 (by decide +kernel)))))
    ⟨0, by norm_num⟩ (by
      change elt (eW.getD 0 []) = heT1P
      rw [hget 0, EB0, ← t1W_eq, elt_t1W]) (T := T5.map elt) ?_ c
    (fun j hj => closure_hs_le (hc j hj)) ?_ (by norm_num) hx ?_ ?_
  · intro t ht
    obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 ht
    simp only [T5, List.mem_cons, List.not_mem_nil, or_false] at hwd
    rcases hwd with rfl | rfl | rfl
    · exact hmem 1 (by norm_num)
    · exact hmem 2 (by norm_num)
    · exact hmem 3 (by norm_num)
  · intro j hj j' hj' h
    exact hinj j hj j' hj' fun t ht => h (elt t) (List.mem_map_of_mem ht)
  · have := hcom 0 (by norm_num)
    rwa [EB0, ← t1W_eq, elt_t1W] at this
  · intro t ht
    obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 ht
    simp only [T5, List.mem_cons, List.not_mem_nil, or_false] at hwd
    rcases hwd with rfl | rfl | rfl
    · exact hcom 1 (by norm_num)
    · exact hcom 2 (by norm_num)
    · exact hcom 3 (by norm_num)

theorem cent_Q
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (hxc : ∀ i : Fin 3, x * elt (qW.getD i []) = elt (qW.getD i []) * x) :
    x ∈ eSub ebasis_Q := by
  have hget : ∀ i, qW.getD i [] = QB.getD i [] := fun i => by rw [qW_eq]
  obtain ⟨c, hc, hinj⟩ := orbRecK_sound (by norm_num) letRep_LU rfl letRep_HC (by norm_num)
    (fun t ht => T7_letters t ht) ch7223o7
  have hmem : ∀ j : ℕ, (hj : j < 4) → elt (QB.getD j []) ∈ eSub ebasis_Q := fun j hj => by
    rw [← hget j]
    exact mem_eSub ebasis_Q ⟨j, hj⟩
  have hcom : ∀ j : ℕ, (hj : j < 3) → x * elt (QB.getD j []) = elt (QB.getD j []) * x :=
    fun j hj => by
      rw [← hget j]
      exact hxc ⟨j, hj⟩
  refine mem_eSub_of_orbit ebasis_Q (fun i => by
      change elt (qW.getD i []) ∈ heP
      rw [hget i]
      exact elt_mem_heP (QB_letters _ (getD_mem (lt_of_lt_of_eq i.2 (by decide +kernel)))))
    ⟨0, by norm_num⟩ (by
      change elt (qW.getD 0 []) = heT1P
      rw [hget 0, QB0, ← t1W_eq, elt_t1W]) (T := T7.map elt) ?_ c
    (fun j hj => closure_hs_le (hc j hj)) ?_ (by norm_num) hx ?_ ?_
  · intro t ht
    obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 ht
    simp only [T7, List.mem_cons, List.not_mem_nil, or_false] at hwd
    rcases hwd with rfl | rfl
    · exact hmem 1 (by norm_num)
    · exact hmem 2 (by norm_num)
  · intro j hj j' hj' h
    exact hinj j hj j' hj' fun t ht => h (elt t) (List.mem_map_of_mem ht)
  · have := hcom 0 (by norm_num)
    rwa [QB0, ← t1W_eq, elt_t1W] at this
  · intro t ht
    obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 ht
    simp only [T7, List.mem_cons, List.not_mem_nil, or_false] at hwd
    rcases hwd with rfl | rfl
    · exact hcom 1 (by norm_num)
    · exact hcom 2 (by norm_num)

end CertificateChecks.KernelHe7223

end
