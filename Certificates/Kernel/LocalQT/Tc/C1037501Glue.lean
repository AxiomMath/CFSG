module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U62
public import Certificates.Kernel.LocalQT.Tc.C1037501
public import CFSG.Certificates.Kernel.LocalQTTcKSound
import Certificates.Kernel.T46K.Letters
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Cert
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CertificateChecks.KD.LQT.C1037501

open CFSG.Fischer CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.T46K CFSG.KC.LQT.TC
  CFSG.KC.LQT.TCK CFSG.KC.LQT.U62G CFSG.KC.PkPow CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.F4.Native CFSG.Sporadic.Fi22.Native CFSG.LocalAnalysis.WeakClosure81
  CFSG.ComponentClassification.RankTwoHypIICover.U62

@[expose] noncomputable def u62L (z : ℤ) : Equiv.Perm (Fin 693) :=
  if z = 0 then 1 else t46G z

theorem u62L_mem (z : ℤ) :
    u62L z ∈ T46 := by
  unfold u62L
  split_ifs
  · exact T46.one_mem
  · exact t46G_mem z

theorem rp_unique {n w P : ℕ} {g h : Equiv.Perm (Fin n)} (hg : RP n w P g) (hh : RP n w P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem rp_idn : RP 693 12 (pidn 693 12) 1 :=
  CFSG.KS.Raw.Orb.prep_pidn (by norm_num) (by norm_num)

theorem pg_LK (l x : ℕ) : pg 12 (mask 12) (tT l) x = LK l x := rfl

theorem gen_rp {j : ℕ} (hj : j < 46) :
    RP 693 12 (tT (2 * j)) (t46G ((j : ℤ) + 1)) := by
  intro x
  have hT := CertificateChecks.KernelT46.gen_TR hj
  have hR := rep_t46G ((j : ℤ) + 1)
  have e : t46Gen ((j : ℤ) + 1) = tvTable (tvGens ())[j]! := by
    unfold t46Gen
    congr 3
  rw [e] at hR
  rw [pg_LK, ← (hT.2 x x.isLt).1, hR x x.isLt, idx_of_lt _ x.isLt, Equiv.Perm.smul_def]

theorem gensFrom_spec : ∀ (G : List ℕ) (j : ℕ), gensFrom G j = true →
    G.length + j = 46 ∧ ∀ k < G.length, G.getD k 0 = tT (2 * (j + k))
  | [], j, h => by
    have : j = 46 := Nat.eq_of_beq_eq_true h
    exact ⟨by simp [this], fun k hk => absurd hk (by simp)⟩
  | g :: G, j, h => by
    have h' : bAnd(Nat.beq g (tT (2 * j)), gensFrom G (j + 1)) = true := h
    obtain ⟨h1, h2⟩ := bAnd_true h'
    obtain ⟨hl, hk⟩ := gensFrom_spec G (j + 1) h2
    refine ⟨by simp; omega, fun k hk' => ?_⟩
    rcases k with _ | k
    · simpa using Nat.eq_of_beq_eq_true h1
    · have := hk k (by simpa using hk')
      simp only [List.getD_cons_succ]
      rw [this]
      congr 2
      omega

theorem gensU_spec {G : List ℕ} (h : gensU G = true) :
    G.length = 46 ∧ ∀ j < 46, G.getD j 0 = tT (2 * j) := by
  obtain ⟨hl, hk⟩ := gensFrom_spec G 0 h
  refine ⟨by simpa using hl, fun j hj => ?_⟩
  rw [hk j (by omega), Nat.zero_add]

section Gens

variable {G : List ℕ}

theorem getD_rp (hG : G.length = 46 ∧ ∀ j < 46, G.getD j 0 = tT (2 * j)) (j : ℕ) :
    RP 693 12 (G.getD j (pidn 693 12)) (t46G ((j : ℤ) + 1)) := by
  by_cases hj : j < 46
  · rw [List.getD_eq_getElem _ _ (by omega), ← List.getD_eq_getElem _ 0 (by omega), hG.2 j hj]
    exact gen_rp hj
  · rw [List.getD_eq_default _ _ (by omega), t46G_eq_one (by omega)]
    exact rp_idn

theorem letG_rp (hG : G.length = 46 ∧ ∀ j < 46, G.getD j 0 = tT (2 * j)) (z : ℤ) :
    RP 693 12 (letG (pidn 693 12) G G z) (u62L z) := by
  rcases z with (_ | j) | k
  · change RP 693 12 (pidn 693 12) (u62L 0)
    rw [u62L, if_pos rfl]
    exact rp_idn
  · change RP 693 12 (getTc (pidn 693 12) G j) _
    have hz : Int.ofNat (j + 1) ≠ 0 := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [getTc_eq, u62L, if_neg hz, t46G_congr (z := Int.ofNat (j + 1)) (z' := (j : ℤ) + 1) (by simp)]
    exact getD_rp hG j
  · change RP 693 12 (getTc (pidn 693 12) G k) _
    rw [getTc_eq, u62L, if_neg (Int.negSucc_ne_zero k),
      t46G_congr (z := Int.negSucc k) (z' := (k : ℤ) + 1) (by rw [Int.natAbs_negSucc]; omega)]
    exact getD_rp hG k

theorem wordU_rp (hG : G.length = 46 ∧ ∀ j < 46, G.getD j 0 = tT (2 * j)) :
    ∀ w : List ℤ, RP 693 12 (wordU G w) (wordG u62L w)
  | [] => by
    change RP 693 12 (pidn 693 12) _
    simpa [wordG] using rp_idn
  | z :: w => by
    change RP 693 12 (strictN (wordU G w)
      (fun q => pcomp 693 12 (mask 12) (letG (pidn 693 12) G G z) q)) _
    rw [sN]
    have e : wordG u62L (z :: w) = u62L z * wordG u62L w := by
      simp [wordG]
    rw [e]
    exact rp_pcomp (by norm_num) (letG_rp hG z) (wordU_rp hG w)

end Gens

theorem phi_rp {Phi : ℕ} (h : phiU Phi = true) :
    RP 693 12 Phi u62Phi := by
  unfold phiU at h
  obtain ⟨-, h⟩ := bAnd_true h
  intro x
  have hx := CFSG.KS.Raw.Orb.allN_iff.1 h x x.isLt
  rw [sB] at hx
  obtain ⟨h1, h2⟩ := bAnd_true hx
  have hy : pg 12 (mask 12) Phi x < 693 := by
    rw [Nat.blt_eq] at h1
    exact h1
  have hc : UC (pg 12 (mask 12) Phi x) = normC (frobU (UC x)) := Nat.eq_of_beq_eq_true h2
  have hrep := phiTab_rep x x.isLt
  rw [idx_of_lt _ x.isLt, Equiv.Perm.smul_def] at hrep
  rw [← hrep]
  have hpt : normC (Gs03U62.frobCode uPts[(x : ℕ)]!) = uPts[pg 12 (mask 12) Phi x]! := by
    rw [CertificateChecks.KernelT46.uPts_get x.isLt, CertificateChecks.KernelT46.uPts_get hy, hc]
    rfl
  have hlt : uPts[pg 12 (mask 12) Phi x]! < 4096 := by
    rw [CertificateChecks.KernelT46.uPts_get hy]
    exact CertificateChecks.KernelT46.UC_lt _
  unfold Gs03U62.phiTab
  rw [ap_ofFn _ x.isLt, hpt, uPos_get hlt, CertificateChecks.KernelT46.idx_uPts hy,
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem nfix_foldr (P : ℕ) : ∀ l : List ℕ,
    l.foldr (fun x c => nIf(Nat.beq (pg 12 (mask 12) P x) x, Nat.succ c, c)) 0 =
      (l.filter fun x => decide (pg 12 (mask 12) P x = x)).length
  | [] => rfl
  | x :: l => by
    rw [List.foldr_cons, nfix_foldr P l, List.filter_cons]
    cases hb : Nat.beq (pg 12 (mask 12) P x) x
    · have : ¬ pg 12 (mask 12) P x = x := fun e => by rw [e, Nat.beq_refl] at hb; cases hb
      simp [this]
    · simp [Nat.eq_of_beq_eq_true hb]

theorem nfix_eq {P : ℕ} {g : Equiv.Perm (Fin 693)} (h : RP 693 12 P g) :
    nfix 693 12 P = gs03FixCount g := by
  unfold nfix
  rw [CFSG.KS.Raw.Orb.foldN_eq, nfix_foldr]
  unfold gs03FixCount
  have e : (Finset.univ.filter fun p : Fin 693 => g p = p).map Fin.valEmbedding =
      (Finset.range 693).filter fun x => pg 12 (mask 12) P x = x := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.isLt, by rw [h b, hb]⟩
    · rintro ⟨ha, hc⟩
      refine ⟨⟨a, ha⟩, Fin.ext ?_, rfl⟩
      rw [← h ⟨a, ha⟩]
      exact hc
  rw [← Finset.card_map Fin.valEmbedding, e]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card]

theorem xw_eq : wordG u62L xw = t46x := by
  simp [wordG, xw, u62L, t46x, pow_succ, mul_assoc]

theorem yw_eq : wordG u62L yw = t46y := by
  simp [wordG, yw, u62L, t46y, pow_succ, mul_assoc]

theorem tcK_parts {n w : ℕ} {G GI : List ℕ} {T TI : ℕ} {ws : List (List ℤ)}
    {prog : List (ℤ × ℤ)} {targets : List ℕ} (h : tcK n w G GI T TI ws prog targets = true) :
    gensTc n w G GI = true ∧ permOK n w (mask w) (n * w) T TI = true := by
  unfold tcK at h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨hp, -⟩ := bAnd_true h
  exact ⟨hg, hp⟩

theorem class_facts {G : List ℕ}
    {Phi R X Y : ℕ} {tw : List ℤ} {fix k : ℕ} {ws : List (List ℤ)} {prog : List (ℤ × ℤ)}
    (hb : baseU G Phi X Y = true) (hc : classU G Phi R tw fix ws prog X Y = true)
    (hk : ws.length = k) :
    ∃ g : Equiv.Perm (Fin 693), (∃ t ∈ T46, g = t * u62Phi) ∧ g * g = 1 ∧
      gs03FixCount g = fix ∧
      ∃ s : Fin k → ↥T46, T46.subtype.range ≤
        Subgroup.closure (Set.range fun i => (T46.subtype (s i))⁻¹ * g * T46.subtype (s i)) := by
  unfold baseU at hb
  obtain ⟨hG, hb⟩ := bAnd_true hb
  obtain ⟨hP, hb⟩ := bAnd_true hb
  obtain ⟨hX, hY⟩ := bAnd_true hb
  unfold classU at hc
  obtain ⟨hR, hc⟩ := bAnd_true hc
  obtain ⟨-, hc⟩ := bAnd_true hc
  obtain ⟨hF, hT⟩ := bAnd_true hc
  have hGs := gensU_spec hG
  have hRr : RP 693 12 R (wordG u62L tw * u62Phi) := by
    rw [Nat.eq_of_beq_eq_true hR]
    exact rp_pcomp (by norm_num) (wordU_rp hGs tw) (phi_rp hP)
  have hXr : RP 693 12 X t46x := by
    rw [Nat.eq_of_beq_eq_true hX, ← xw_eq]
    exact wordU_rp hGs xw
  have hYr : RP 693 12 Y t46y := by
    rw [Nat.eq_of_beq_eq_true hY, ← yw_eq]
    exact wordU_rp hGs yw
  have hT' := tcK_sound hT
  obtain ⟨hg, hp⟩ := tcK_parts hT
  obtain ⟨τ, hτP, hτR, -⟩ := of_permOK hp
  have hτ : τ = wordG u62L tw * u62Phi := rp_unique hτR hRr
  have hτi : τ = τ⁻¹ := CFSG.Monster.B.Co2.Rep.unique hτP.1 hτP.2
  obtain ⟨hl, hz⟩ := gensTc_sound G G hg
  have hK : CFSG.QuasithinUnique.Setup.X1.RegIn 693 T46
      ((G.zip G).map fun p => (unpack 693 12 p.1, unpack 693 12 p.2)) := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    obtain ⟨g, h1, h2, -⟩ := of_permOK (hz p hp)
    refine ⟨g, ?_, h1⟩
    obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem (List.of_mem_zip hp).1
    have hj' := getD_rp hGs j
    rw [List.getD_eq_getElem _ _ hj, hgj] at hj'
    rw [rp_unique h2 hj']
    exact t46G_mem _
  obtain ⟨gs, hlen, hgs, htarg⟩ :=
    CFSG.QuasithinUnique.Setup.X1.threeConj_sound hK hτP hT'
  have hxm := htarg _ (List.mem_map_of_mem List.mem_cons_self) t46x
    (CFSG.KS.Raw.Orb.rep_unpack hXr)
  have hym := htarg _ (List.mem_map_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)) t46y
    (CFSG.KS.Raw.Orb.rep_unpack hYr)
  have hidx : ∀ i : Fin k, i.val < gs.length := fun i => by omega
  let s : Fin k → ↥T46 := fun i => ⟨(gs[i.val]'(hidx i))⁻¹, T46.inv_mem (hgs _ (List.getElem_mem _))⟩
  have hle : Subgroup.closure (CFSG.QuasithinUnique.Setup.X1.conjSet gs {τ}) ≤
      Subgroup.closure (Set.range fun i => (T46.subtype (s i))⁻¹ * τ * T46.subtype (s i)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, t, ht, rfl⟩
    rw [Set.mem_singleton_iff] at ht
    subst ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    refine Subgroup.subset_closure ⟨⟨i, by omega⟩, ?_⟩
    simp [s]
  refine ⟨τ, ⟨wordG u62L tw, t46_wordG_mem u62L_mem tw, hτ⟩, ?_, ?_, s, ?_⟩
  · nth_rewrite 2 [hτi]
    exact mul_inv_cancel τ
  · rw [← nfix_eq hτR]
    exact Nat.eq_of_beq_eq_true hF
  · rw [Subgroup.range_subtype]
    refine le_trans T46_le_closure (le_trans ?_ hle)
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hxm
    · exact hym

theorem gs03AlphaU6_of_facts
    {g₀ g₁ : Equiv.Perm (Fin 693)}
    (hf : U62RepFacts g₀ g₁) : GS03AlphaU6 := by
  classical
  intro G _ _ S hS hC t n f hR hlie x hx hxS
  obtain ⟨rfl, rfl, rfl⟩ := hR
  have : S.Normal := hS
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U62.nonempty_mulEquiv_T46 hlie
  have hF : U62Facts := u62_facts
  obtain ⟨T, hTcard, hTconj, hTgen⟩ := gs03_of_autGenBound
    (gs03_u62_autGenBound hF (gs03_u62_hgen hF hf)) S hC e hx
    (fun _ => gs03_action_not_inner S hC e hxS)
  exact ⟨T, by simpa [gs03Bound] using hTcard, hTconj, hTgen⟩

theorem gs03AlphaU6_kernel :
    GS03AlphaU6 := by
  obtain ⟨g₀, h0t, h0s, h0f, h0g⟩ := class_facts (k := 4) hBase hC0 (by decide)
  obtain ⟨g₁, h1t, h1s, h1f, h1g⟩ := class_facts (k := 3) hBase hC1 (by decide)
  exact gs03AlphaU6_of_facts ⟨h0t, h1t, h0s, h1s, by rw [h0f, h1f]; decide, h0g, h1g⟩

end CertificateChecks.KD.LQT.C1037501

end
