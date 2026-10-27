
module

public import Certificates.Kernel.MonsterB.Short3014Checks
public import CFSG.Certificates.Kernel.MonsterB.ShortSearchSound
public import CFSG.Certificates.Kernel.SortTreeSound
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
public import CFSG.Monster.B.Short.TransitivityBase
public import CFSG.Monster.VisCert.FrameOrbit

public section

namespace CertificateChecks.Short3014

open CFSG.KC.SortTree CFSG.KC.KSearch CFSG.KC.Bfs CFSG.KLie.CT CFSG.Monster.VisCert
  CFSG.Monster.VisCert.Native CFSG.Monster CFSG.Monster.B.Short

theorem xorK_actGo (rows : Array ℕ) (v : ℕ) (f : ℕ → ℕ) :
    ∀ n, (∀ t < n, f t = rows[t]!) →
      CFSG.KC.U6Orb.xorK n (fun t => nIf(bit v t, f t, 0)) = Native.actGo rows v n 0
  | 0, _ => rfl
  | n + 1, h => by
    rw [CFSG.KC.U6Orb.xorK_succ, xorK_actGo rows v f n (fun t ht => h t (by omega)), Native.actGo,
      actGo_acc rows v n, CFSG.KC.U6Orb.bit_eq, h n (by omega)]
    cases v.testBit n
    · simp
    · simp only [↓reduceIte, Nat.zero_xor]
      rw [actGo_acc rows v n rows[n]!, Nat.xor_comm]

theorem actF_eq {g : ℕ} (hg : g < 15) (v : ℕ) : actF g v = gimg g v := by
  have h := fr_ok
  rw [allN_iff] at h
  have h2 := (allN_iff _ _).1 (h g hg)
  unfold actF gimg Native.actRows
  refine xorK_actGo _ v _ 24 fun t ht => ?_
  exact beq_iff.1 (h2 t ht)

theorem tree_ok : treeOK actF 15 (fun _ => true) 12288 recS 98280 24 4 17 2048 48 = true := by
  have hs : ∀ k < 8, slice (6 * k) 6 = true := by
    intro k hk
    interval_cases k
    exacts [t0, t1, t2, t3, t4, t5, t6, t7]
  rw [treeOK, andB_true_iff, ble_iff, allN_iff]
  refine ⟨by norm_num, fun c hc => ?_⟩
  have := (allN_iff _ _).1 (hs (c / 6) (by omega)) (c % 6) (Nat.mod_lt _ (by norm_num))
  change chunk (6 * (c / 6) + c % 6) = true at this
  rwa [Nat.div_add_mod] at this

theorem tree_rin {act : ℕ → ℕ → ℕ} {ng root n wv wl wp : ℕ} {valid : ℕ → Bool}
    {rec : ℕ → ℕ} (h : ∀ i < n, recOK act ng valid root rec n wv wl wp (rec i) = true) :
    ∀ i < n, RIn act ng root (levF wv wl (rec i)) (valF wv (rec i)) := by
  suffices H : ∀ L i, i < n → levF wv wl (rec i) ≤ L →
      RIn act ng root (levF wv wl (rec i)) (valF wv (rec i)) from fun i hi => H _ i hi le_rfl
  intro L
  induction L with
  | zero =>
    intro i hi hL
    have h0 : levF wv wl (rec i) = 0 := by omega
    rw [h0, (recOK_spec (act := act) (ng := ng) (valid := valid) (root := root) (rec := rec)
      (n := n) (wv := wv) (wl := wl) (wp := wp) (h i hi)).2.1 h0]
    exact RIn.root
  | succ L ih =>
    intro i hi hL
    by_cases h0 : levF wv wl (rec i) = 0
    · exact ih i hi (by omega)
    · obtain ⟨hp, hg, hlev, e⟩ := (recOK_spec (act := act) (ng := ng) (valid := valid) (root := root)
        (rec := rec) (n := n) (wv := wv) (wl := wl) (wp := wp) (h i hi)).2.2 h0
      have hr := ih _ hp (by omega)
      rw [← e]
      have := RIn.step _ hg hr
      exact this.le (by omega)

theorem levF_lt (r : ℕ) : levF 24 4 r < 16 := by
  change Nat.land (Nat.shiftRight r 24) (maskN 4) < 16
  exact lt_of_le_of_lt (Nat.and_le_right) (by decide)

theorem reach_of_eq {F G : ℕ → ℕ → ℕ} {m s : ℕ} (hFG : ∀ g < m, ∀ v, F g v = G g v) {u : ℕ}
    (h : Reach F m s u) : Reach G m s u := by
  induction h with
  | root => exact Reach.root
  | step g hg _ ih => rw [hFG g hg]; exact Reach.step g hg ih

theorem rin_of_eq {F G : ℕ → ℕ → ℕ} {m s k : ℕ} (hFG : ∀ g < m, ∀ v, F g v = G g v) {u : ℕ}
    (h : RIn F m s k u) : RIn G m s k u := by
  induction h with
  | root => exact RIn.root
  | mono _ ih => exact ih.mono
  | step g hg _ ih => rw [hFG g hg]; exact RIn.step g hg ih

theorem reach_short {u : ℕ} (h : Reach gimg 15 12288 u) : u < 2 ^ 24 ∧ dec u ∈ shortSet := by
  induction h with
  | root =>
    refine ⟨by norm_num, ?_⟩
    have e := dec_shortSeed
    exact e ▸ classOf_vMinus_mem_shortSet
  | step g hg _ ih =>
    refine ⟨gimg_lt hg _, ?_⟩
    rw [kGenN_smul_dec g hg]
    exact smul_mem_shortSet_of_mem_Hvis (Kvis_le_Hvis (kGenN_mem_Kvis hg)) ih.2

noncomputable def treeSet : Finset ℕ := (Finset.range 98280).image fun i => valF 24 (recS i)

theorem mem_treeSet (x : ℕ) : x ∈ treeSet ↔ ∃ i < 98280, valF 24 (recS i) = x := by
  simp [treeSet]

theorem vals_lt : ∀ i j, i < j → j < 98280 → valF 24 (recS i) < valF 24 (recS j) :=
  (tree_sound tree_ok).2.2.1

theorem treeSet_card : treeSet.card = 98280 := by
  rw [treeSet, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb e
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact absurd e (ne_of_lt (vals_lt a b hab hb))
  · rfl
  · exact absurd e (ne_of_gt (vals_lt b a hab ha))

theorem treeSet_reach {x : ℕ} (hx : x ∈ treeSet) : Reach gimg 15 12288 x := by
  obtain ⟨i, hi, rfl⟩ := (mem_treeSet x).1 hx
  exact reach_of_eq (fun g hg v => actF_eq hg v) ((tree_sound tree_ok).1 i hi)

theorem reach_iff (u : ℕ) : Reach gimg 15 12288 u ↔ ∃ i < 98280, valF 24 (recS i) = u := by
  refine Iff.trans ?_ (mem_treeSet u)
  refine ⟨fun hu => ?_, treeSet_reach⟩
  by_contra hnot
  have hT' : ∀ x ∈ insert u treeSet, x < 2 ^ 24 ∧ dec x ∈ shortSet := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact reach_short hu
    · exact reach_short (treeSet_reach hx)
  have hinj : Set.InjOn dec (insert u treeSet : Finset ℕ) := fun a ha b hb e =>
    dec_inj a b (hT' a ha).1 (hT' b hb).1 e
  have hsub : dec '' (insert u treeSet : Finset ℕ) ⊆ shortSet := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hT' x hx).2
  have hfin : shortSet.Finite := Set.finite_of_ncard_pos (by rw [ncard_shortSet]; norm_num)
  have := Set.ncard_le_ncard hsub hfin
  rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_insert_of_notMem hnot,
    treeSet_card, ncard_shortSet] at this
  omega

theorem orbit : ∃ S : Finset ℕ, (∀ u, Reach gimg 15 12288 u ↔ u ∈ S) ∧ S.card = 98280 ∧
    ∀ u ∈ S, RIn gimg 15 12288 253 u := by
  obtain ⟨hrec, -⟩ := tree_spec tree_ok
  refine ⟨treeSet, fun u => (reach_iff u).trans (mem_treeSet u).symm, treeSet_card,
    fun u hu => ?_⟩
  obtain ⟨i, hi, rfl⟩ := (mem_treeSet u).1 hu
  exact rin_of_eq (fun g hg v => actF_eq hg v)
    ((tree_rin hrec i hi).le (by have := levF_lt (recS i); omega))

@[expose] noncomputable def memS (u : ℕ) : Bool :=
  CFSG.KC.Co1M.orbMemK 98280 (fun i => valF 24 (recS i)) 17 u

theorem memS_iff (u : ℕ) : memS u = true ↔ Reach gimg 15 12288 u := by
  rw [reach_iff]
  unfold memS CFSG.KC.Co1M.orbMemK
  rw [Nat.beq_eq]
  constructor
  · intro h
    exact ⟨_, CFSG.KC.Co1M.orbBsK_lt 17 0 (by norm_num), h⟩
  · rintro ⟨r, hr, rfl⟩
    rw [CFSG.KC.Co1M.orbBsK_find vals_lt hr rfl 17 0 (Nat.zero_le _) (by omega)]

theorem klev_iff (u : ℕ) :
    rd8 (CFSG.Monster.B.Short.Native.shortTables ()).klev u ≠ 0 ↔ Reach gimg 15 12288 u := by
  have hN : (1 <<< 24 : ℕ) = 2 ^ 24 := by norm_num
  have hFG : ∀ g < 15, ∀ v < 1 <<< 24, shortF g v = gimg g v := fun g hg v hv =>
    fastAct_frame hg (by rw [← hN]; exact hv)
  have hG : ∀ g < 15, ∀ v < 1 <<< 24, gimg g v < 1 <<< 24 := fun g hg v _ => by
    rw [hN]
    exact gimg_lt hg v
  have hseed : (12288 : ℕ) < 1 <<< 24 := by rw [hN]; norm_num
  have hR := reach_congr hseed hG hFG
  obtain ⟨S, hS, hcard, hD⟩ := orbit
  obtain ⟨-, hne, -, -⟩ := kRun_spec (F := shortF) (m := 15) (N := 1 <<< 24)
    (seed := 12288) hseed (fun g hg v hv => by rw [hFG g hg v hv]; exact hG g hg v hv)
    (by norm_num) (by norm_num)
    ⟨S, fun u hu => (hS u).1 ((hR u).1 hu), by rw [hcard, hN]; norm_num⟩
    (fun u hu => rin_congr hseed hG hFG (hD u ((hS u).1 ((hR u).1 hu))))
  rw [shortTables_eq]
  generalize kRun shortF 15 (1 <<< 24) 12288 = r at hne ⊢
  obtain ⟨lev, lab, par, q, qh⟩ := r
  dsimp only at hne ⊢
  exact (hne u).trans (hR u)

end CertificateChecks.Short3014

end
