module

public import Certificates.Kernel.StdOdd.CentOrbBlkSound
public import Certificates.Kernel.StdOdd.CentOrbCensus
public import Certificates.Kernel.StdOdd.CentOrbInv

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit CFSG.KS.StdOdd.Chain
  CFSG.KD.StdOdd.Orbit CFSG.KC.Misc.E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.Existence.StdOdd.Cert Matrix

theorem tauR_tau : ∀ (Ms Ds : List ℕ), stagesOK Ds Ms = true →
    ∀ q, tauR Ds Ms (tau Ds Ms q) = q
  | [], Ds, _, q => by cases Ds <;> rfl
  | _ :: _, [], _, q => rfl
  | m :: Ms, d :: Ds, h, q => by
    obtain ⟨h1, h2⟩ := disj_of_stagesOK h
    change tauR Ds Ms (swp d m (swp d m (tau Ds Ms q))) = q
    rw [swp_swp h1, tauR_tau Ms Ds h2]

theorem iterate_mulVecK (M : M78) : ∀ (k : ℕ) (u : Fin 78 → K),
    (fun v => M *ᵥ v)^[k] u = M ^ k *ᵥ u
  | 0, u => by simp
  | k + 1, u => by
    rw [Function.iterate_succ_apply', iterate_mulVecK M k u, mulVec_mulVec, ← pow_succ']

theorem orbNetOK_sound {Ds Ms PL : List ℕ} {X : ℕ} {U : List ℕ} {m p g s : ℕ}
    (h : orbNetOK Ds Ms PL X U m p g s = true) :
    ∀ j < g, Nat.beq (net Ds Ms (nthN PL (g * s + j))) (orbPlane X U m p (g * s + j)) = true := by
  suffices H : ∀ n, (Nat.rec (motive := fun _ => Bool) true (fun j ih => andB (forceB
      (Nat.add (Nat.mul g s) j) fun c => Nat.beq (net Ds Ms (nthN PL c)) (orbPlane X U m p c)) ih)
        n : Bool) = true → ∀ j < n,
        Nat.beq (net Ds Ms (nthN PL (g * s + j))) (orbPlane X U m p (g * s + j)) = true from
    H g h
  intro n
  induction n with
  | zero => intro _ j hj; omega
  | succ n ih =>
    intro hn j hj
    change andB (forceB (Nat.add (Nat.mul g s) n) fun c =>
      Nat.beq (net Ds Ms (nthN PL c)) (orbPlane X U m p c)) _ = true at hn
    rw [andB_eq, Bool.and_eq_true, forceB_eq] at hn
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih hn.2 j hj
    · exact hn.1

namespace CentData

variable (D : CentData)

theorem card_prof_orb {A B : ℕ} (hX : Rep (D.xB A B) (wM D.xw))
    (hts1 : ∀ q ∈ D.K1, q.2 = 0 ∨ q.2 = 3 ∨ q.2 = 4 ∨ q.2 = 5)
    {PL Ds Ms U cs : List ℕ} {m p f Q d : ℕ} (hp : 0 < p) (hUl : lenN U = 156)
    (hv : stagesOK Ds Ms = true) (hfull : Nat.beq (net Ds Ms (full (p * m + f))) (full (p * m + f)) = true)
    (hnet : ∀ c < 156, Nat.beq (net Ds Ms (nthN PL c)) (orbPlane (D.xB A B) U m p c) = true)
    (hQ : m ≤ Q * 262144) (hch : ∀ q < Q, D.orbChunkB d U A B m cs q = true)
    (hfix : D.orbFixB U A B m f = true) :
    ((Finset.range (p * m + f)).filter fun i =>
      ∀ k ∈ D.K1, rhoC (ptK PL i) (wM D.xw ^ k.1 *ᵥ ptK PL i) = k.2).card =
        p * ∑ q ∈ Finset.range Q, nthN cs q := by
  set P : (Fin 78 → K) → Prop := fun u => ∀ k ∈ D.K1, rhoC u (wM D.xw ^ k.1 *ᵥ u) = k.2 with hPdef
  set τ := tau Ds Ms with hτ
  have hbit : ∀ c < 156, ∀ i, (nthN PL c).testBit (τ i) =
      (orbPlane (D.xB A B) U m p c).testBit i := by
    intro c hc i
    rw [← Nat.eq_of_beq_eq_true (hnet c hc), testBit_net Ms Ds hv]
  have hblk : ∀ k < p, ∀ j < m, ptK PL (τ (k * m + j)) = wM D.xw ^ k *ᵥ ptK U j := by
    intro k hk j hj
    have hg : blowM (wM D.xw ^ k) = matB (powB (D.xB A B) k) := by
      rw [matB_eq_decB, (rep_powB hX k).2]
    have hb : ptB PL (τ (k * m + j)) = matB (powB (D.xB A B) k) *ᵥ ptB U j := by
      funext c
      rw [ptB_eq, hbit c c.2, testBit_orbPlane_blk hk hj]
      exact rowX_bit hUl _ c j
    exact flat_inj (by rw [flat_ptK, hb, flat_mulVec, hg, flat_ptK])
  have hrep : ∀ j < m, ptK PL (τ j) = ptK U j := by
    intro j hj
    have := hblk 0 hp j hj
    rwa [Nat.zero_mul, Nat.zero_add, pow_zero, one_mulVec] at this
  have hfx : ∀ j, ptK PL (τ (p * m + j)) = ptK U (m + j) := by
    intro j
    refine ptB_inj (funext fun c => ?_)
    rw [ptB_eq, ptB_eq, hbit c c.2, testBit_orbPlane_fix]
  have hlt := tau_lt_iff hv hfull
  rw [← cens_perm (n := p * m + f) (ptK PL) (fun i => ptK PL (τ i)) τ P (fun i hi => (hlt i).2 hi)
    (fun i _ j _ h => by rw [← tauR_tau Ms Ds hv i, ← tauR_tau Ms Ds hv j]; exact congrArg _ h)
    (fun _ _ => rfl)]
  rw [Finset.range_add_eq_union, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.disjoint_range_addLeftEmbedding _ _)),
    cens_blocks (fun i => ptK PL (τ i)) (fun v => wM D.xw *ᵥ v) P (prof_wM D.xw D.K1)
      (fun k hk j hj => by rw [hblk k hk j hj, hrep j hj, iterate_mulVecK])]
  have htail : (Finset.filter (fun i => P (ptK PL (τ i)))
      (Finset.map (addLeftEmbedding (p * m)) (Finset.range f))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi hPi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    have hj' : j < f := Finset.mem_range.1 hj
    rw [addLeftEmbedding_apply, hfx] at hPi
    have h0 := congrArg (fun x => x.testBit j) (Nat.eq_of_beq_eq_true hfix)
    have hpr := prof_K (U := chunkPl U m f) hX (by rw [lenN_chunkPl, hUl]) f D.K1 hts1 j
    rw [ptB_inj (ptB_chunkPl U m f j hj')] at hpr
    have : (profAll (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd) (chunkPl U m f) f
        Form.fmPk Form.brPk).testBit j = true := hpr.2 ⟨hj', hPi⟩
    change (profAll (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd) (chunkPl U m f) f
        Form.fmPk Form.brPk).testBit j = (0 : ℕ).testBit j at h0
    rw [this, Nat.zero_testBit] at h0
    exact Bool.noConfusion h0
  rw [htail, Nat.add_zero]
  congr 1
  rw [Finset.filter_congr fun j hj => by rw [hrep j (Finset.mem_range.1 hj)]]
  rw [card_filter_chunks _ 262144 m Q hQ]
  refine Finset.sum_congr rfl fun q hq => ?_
  have h := hch q (Finset.mem_range.1 hq)
  unfold CentData.orbChunkB at h
  rw [forceB_eq] at h
  set w := Nat.min 262144 (Nat.sub m (Nat.mul q 262144)) with hw
  have hw' : w = min 262144 (m - q * 262144) := rfl
  set V := chunkPl U (Nat.mul q 262144) w with hV
  have hVl : lenN V = 156 := by rw [hV, lenN_chunkPl, hUl]
  have hpr := prof_K hX hVl w D.K1 hts1
  have hlt' : profAll (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd) V w Form.fmPk Form.brPk <
      2 ^ w := testBit_lt_of fun i hi => ((hpr i).1 hi).1
  have hc := popK_sound _ _ w (popK_of_popHB h) hlt'
  rw [← hw', ← hc]
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  have hi' : i < w := Finset.mem_range.1 hi
  have hpt' : ptK V i = ptK U (q * 262144 + i) :=
    ptB_inj (ptB_chunkPl U (Nat.mul q 262144) w i hi')
  rw [hpr i, hpt']
  exact ⟨fun h => ⟨hi', h⟩, fun h => h.2⟩

end CentData

end CFSG.KD.StdOdd.Cent

end
