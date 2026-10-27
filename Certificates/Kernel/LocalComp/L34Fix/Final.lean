module

public import Certificates.Kernel.LocalComp.L34Fix.Chk
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34DWordSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Fix

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KC.L34KSnd CFSG.KC.L34Scan CFSG.KC.L34Two CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CertificateChecks.KernelLC.L34Cert
open CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen
open CFSG.KLie.CT (andB orB notB)

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem exists_of_notB_allN {n : Nat} {f : Nat → Bool} (h : notB (allN n f) = true) :
    ∃ k < n, f k = false := by
  rw [notB_iff] at h
  by_contra hc
  push Not at hc
  have : allN n f = true := CFSG.KS.Raw.Orb.allN_iff.2 fun k hk => by
    have := hc k hk
    cases e : f k
    · exact absurd e this
    · rfl
  rw [this] at h
  exact absurd h (by decide)

theorem encR : Enumerates R (pts 42 6 241920 L34R.T).toList := by
  have h := enumerates_R
  rwa [enumR, hR.1] at h

theorem encS : Enumerates S (pts 42 6 20160 L34S.T).toList := by
  have h := enumerates_S
  rwa [enumS, hS.1] at h

theorem elt_of {H : Subgroup (Equiv.Perm (Fin 42))} {N : Nat} {T : Nat → Nat}
    (hE : Enumerates H (pts 42 6 N T).toList) {i : Nat} (hi : i < N) :
    ∃ g ∈ H, TabRep (unpack 42 6 (T i)) g := by
  obtain ⟨g, hg, hr⟩ := hE.sound _ (getElem!_mem (by rw [size_pts]; exact hi))
  rw [pts_get' hi] at hr
  exact ⟨g, hg, hr⟩

theorem pos_of {H : Subgroup (Equiv.Perm (Fin 42))} {N : Nat} {T : Nat → Nat}
    (hE : Enumerates H (pts 42 6 N T).toList) {g : Equiv.Perm (Fin 42)} (hg : g ∈ H) :
    ∃ i < N, TabRep (unpack 42 6 (T i)) g := by
  obtain ⟨t, ht, hr⟩ := hE.complete g hg
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
  rw [size_pts] at hi
  rw [pts_get' hi] at hr
  exact ⟨i, hi, hr⟩

theorem gen_of {H : Subgroup (Equiv.Perm (Fin 42))} {N : Nat} {T : Nat → Nat}
    (hE : Enumerates H (pts 42 6 N T).toList) {i X : Nat} (hi : Nat.blt i N = true)
    (h : Nat.beq (T i) X = true) : ∃ g ∈ H, TabRep (unpack 42 6 X) g := by
  rw [← Nat.eq_of_beq_eq_true h]
  exact elt_of hE (lt_of_blt hi)

theorem hpH : ∀ i < 27, penumPtK 42 6 (mask 6) (42 * 6) false L34FH.G L34FH.GI 2 27 L34FH.T
    L34FH.PL L34FH.POS L34FH.SRT L34FH.SRI i = true := fun i hi =>
  penumSl_spec kH_sl i (Nat.zero_le _) (by omega) hi

theorem encH : enumOK 42 hGens (penumRec 42 6 27 L34FH.T L34FH.PL) = true :=
  (penumK_left_sound hsz42 (gensOK_of kH_gens) kH_hd hpH).2

theorem mrec : ∀ k < 4, GensOK 42 6 2 (L34FM.G k) mGens[k]! ∧
    (∃ E : Enum, E.tabs = pts 42 6 9 (L34FM.T k) ∧ enumOK 42 mGens[k]! E = true) ∧
    ∀ q < 9, canonK 42 6 (mask 6) (42 * 6) (L34FM.T k q) = true := by
  intro k hk
  interval_cases k
  · have hp : ∀ i < 9, penumPtK 42 6 (mask 6) (42 * 6) false L34FM0.G L34FM0.GI 2 9 L34FM0.T
        L34FM0.PL L34FM0.POS L34FM0.SRT L34FM0.SRI i = true := fun i hi =>
      penumSl_spec kM0_sl i (Nat.zero_le _) (by omega) hi
    exact ⟨gensOK_of kM0_gens, ⟨_, rfl, (penumK_left_sound hsz42 (gensOK_of kM0_gens) kM0_hd hp).2⟩,
      fun q hq => penumPt_canon (hp q hq)⟩
  · have hp : ∀ i < 9, penumPtK 42 6 (mask 6) (42 * 6) false L34FM1.G L34FM1.GI 2 9 L34FM1.T
        L34FM1.PL L34FM1.POS L34FM1.SRT L34FM1.SRI i = true := fun i hi =>
      penumSl_spec kM1_sl i (Nat.zero_le _) (by omega) hi
    exact ⟨gensOK_of kM1_gens, ⟨_, rfl, (penumK_left_sound hsz42 (gensOK_of kM1_gens) kM1_hd hp).2⟩,
      fun q hq => penumPt_canon (hp q hq)⟩
  · have hp : ∀ i < 9, penumPtK 42 6 (mask 6) (42 * 6) false L34FM2.G L34FM2.GI 2 9 L34FM2.T
        L34FM2.PL L34FM2.POS L34FM2.SRT L34FM2.SRI i = true := fun i hi =>
      penumSl_spec kM2_sl i (Nat.zero_le _) (by omega) hi
    exact ⟨gensOK_of kM2_gens, ⟨_, rfl, (penumK_left_sound hsz42 (gensOK_of kM2_gens) kM2_hd hp).2⟩,
      fun q hq => penumPt_canon (hp q hq)⟩
  · have hp : ∀ i < 9, penumPtK 42 6 (mask 6) (42 * 6) false L34FM3.G L34FM3.GI 2 9 L34FM3.T
        L34FM3.PL L34FM3.POS L34FM3.SRT L34FM3.SRI i = true := fun i hi =>
      penumSl_spec kM3_sl i (Nat.zero_le _) (by omega) hi
    exact ⟨gensOK_of kM3_gens, ⟨_, rfl, (penumK_left_sound hsz42 (gensOK_of kM3_gens) kM3_hd hp).2⟩,
      fun q hq => penumPt_canon (hp q hq)⟩

@[expose] def Hs : Set (Equiv.Perm (Fin 42)) := {x | ∃ j < hGens.size, TabRep hGens[j]! x}

@[expose] def Ms (k : Nat) : Set (Equiv.Perm (Fin 42)) :=
  {x | ∃ j < (mGens[k]!).size, TabRep (mGens[k]!)[j]! x}

theorem kR' : (∀ n < 10, Nat.blt (L34FW.RI.getD n 0) 241920 = true) ∧
    (∀ j < 2, Nat.beq (L34R.T (L34FW.RI.getD j 0)) (L34FH.G j) = true) ∧
    ∀ k < 4, ∀ j < 2,
      Nat.beq (L34R.T (L34FW.RI.getD (Nat.add (Nat.add (Nat.mul 2 k) j) 2) 0)) (L34FM.G k j) =
        true := by
  obtain ⟨h1, h⟩ := andB_iff.1 kR
  obtain ⟨h2, h3⟩ := andB_iff.1 h
  exact ⟨CFSG.KS.Raw.Orb.allN_iff.1 h1, CFSG.KS.Raw.Orb.allN_iff.1 h2,
    fun k hk => CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h3 k hk)⟩

theorem hgensH : ∀ j < hGens.size, ∃ a ∈ Hs, TabRep hGens[j]! a := by
  intro j hj
  have hj2 : j < 2 := by rw [(gensOK_of kH_gens).1] at hj; exact hj
  obtain ⟨g, -, hr⟩ := gen_of encR (kR'.1 j (by omega)) (kR'.2.1 j hj2)
  rw [← ((gensOK_of kH_gens).2 j hj2).1] at hr
  exact ⟨g, ⟨j, hj, hr⟩, hr⟩

theorem hgensM {k : Nat} (hk : k < 4) : ∀ j < (mGens[k]!).size, ∃ a ∈ Ms k,
    TabRep (mGens[k]!)[j]! a := by
  intro j hj
  have hj2 : j < 2 := by rw [(mrec k hk).1.1] at hj; exact hj
  obtain ⟨g, -, hr⟩ := gen_of encR (kR'.1 _ (by change 2 * k + j + 2 < 10; omega))
    (kR'.2.2 k hk j hj2)
  rw [← ((mrec k hk).1.2 j hj2).1] at hr
  exact ⟨g, ⟨j, hj, hr⟩, hr⟩

theorem encHs : Enumerates (Subgroup.closure Hs) (pts 42 6 27 L34FH.T).toList :=
  enumerates_closure (fun a ha => ha) hgensH encH

theorem encMs {k : Nat} (hk : k < 4) :
    Enumerates (Subgroup.closure (Ms k)) (pts 42 6 9 (L34FM.T k)).toList := by
  obtain ⟨E, hE, hok⟩ := (mrec k hk).2.1
  have h := enumerates_closure (fun a ha => ha) (hgensM hk) hok
  rwa [hE] at h

theorem fix_gen {kk : Nat} (hkk : kk < 3) :
    Subgroup.closure {s | s ∈ S ∧ ∃ r ∈ Subgroup.closure (Ms (Nat.succ kk)), r ≠ 1 ∧
      r * s * r⁻¹ = s} = S := by
  set F := {s | s ∈ S ∧ ∃ r ∈ Subgroup.closure (Ms (Nat.succ kk)), r ≠ 1 ∧ r * s * r⁻¹ = s}
  obtain ⟨h1, h2⟩ := andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kFix kk hkk)
  have hM := encMs (k := Nat.succ kk) (by omega)
  have hA : ∀ j < 2, canonK 42 6 (mask 6) (42 * 6) (L34FW.A (Nat.succ kk) j) = true ∧
      ∃ a ∈ Subgroup.closure F, TabRep (unpack 42 6 (L34FW.A (Nat.succ kk) j)) a := by
    intro j hj
    obtain ⟨b1, h⟩ := andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h1 j hj)
    obtain ⟨b2, h⟩ := andB_iff.1 h
    obtain ⟨hne, hc⟩ := andB_iff.1 h
    have eA : L34FW.A (Nat.succ kk) j =
        L34S.T (L34FW.FI.getD (Nat.add (Nat.mul 2 kk) j) 0) := rfl
    have cs : canonK 42 6 (mask 6) (42 * 6) (L34FW.A (Nat.succ kk) j) = true := by
      rw [eA]
      exact pinS.canon _ (lt_of_blt b1)
    obtain ⟨s, hsS, hs⟩ := elt_of encS (lt_of_blt b1)
    rw [← eA] at hs
    have hq := lt_of_blt b2
    obtain ⟨r, hrM, hr⟩ := elt_of hM hq
    have cr := (mrec (Nat.succ kk) (by omega)).2.2 _ hq
    refine ⟨cs, s, Subgroup.subset_closure ⟨hsS, r, hrM, fun hr1 => ?_, ?_⟩, hs⟩
    · rw [hr1] at hr
      have e : unpack 42 6 (L34FM.T (Nat.succ kk) (L34FW.FQ.getD (Nat.add (Nat.mul 2 kk) j) 0)) =
          unpack 42 6 (pidn 42 6) := by
        rw [← idTab_unpack' hsz42]
        exact hr.tab_eq TabRep.idTab
      rw [unpack_inj' cr (canon_pidn hsz42) e, notB_iff, Nat.beq_refl] at hne
      exact absurd hne (by decide)
    · have hsr : s * r = r * s := ((hs.comp hr).eq_iff (hr.comp hs)).1 ((commPt_iff cs cr).1 hc)
      calc r * s * r⁻¹ = s * r * r⁻¹ := by rw [hsr]
        _ = s := by group
  have hSdef : S = Subgroup.closure {g₁, g₂, g₃} := rfl
  refine le_antisymm ((Subgroup.closure_le S).2 fun s hs => hs.1) ?_
  rw [hSdef, Subgroup.closure_le]
  intro a ha
  obtain ⟨i, hi, hia⟩ := gensS_cover a ha
  have hi3 : i < 3 := hi
  rw [bindS.2 i hi3] at hia
  exact mem_of_dwordK (m := 2) (by decide) hA hia (CFSG.KS.Raw.Orb.allN_iff.1 h2 i hi3)

theorem facts9695 : ∃ (H₀ : Subgroup (Equiv.Perm (Fin 42))) (M : Fin 4 → Subgroup (Equiv.Perm (Fin 42))),
    H₀ ≤ R ∧ Nat.card H₀ = 27 ∧ (∀ k, Nat.card (M k) = 9) ∧
    (∀ u ∈ H₀, ∀ v ∈ H₀, u * v = v * u → ∃ k, u ∈ M k ∧ v ∈ M k) ∧ M 0 ≤ S ∧
    ∀ k : Fin 4, k ≠ 0 →
      Subgroup.closure {s | s ∈ S ∧ ∃ r ∈ M k, r ≠ 1 ∧ r * s * r⁻¹ = s} = S := by
  refine ⟨Subgroup.closure Hs, fun k => Subgroup.closure (Ms k.val), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨j, hj, hx⟩
    have hj2 : j < 2 := by rw [(gensOK_of kH_gens).1] at hj; exact hj
    obtain ⟨g, hgR, hgr⟩ := gen_of encR (kR'.1 j (by omega)) (kR'.2.1 j hj2)
    rw [← ((gensOK_of kH_gens).2 j hj2).1] at hgr
    rw [hx.perm_eq hgr]
    exact hgR
  · rw [encHs.card, Array.length_toList, size_pts]
  · intro k
    rw [(encMs k.2).card, Array.length_toList, size_pts]
  · intro u hu v hv huv
    obtain ⟨i, hi, hui⟩ := pos_of encHs hu
    obtain ⟨j, hj, hvj⟩ := pos_of encHs hv
    have ci := hpH i hi
    have cj := hpH j hj
    have hc : commPt 42 6 (L34FH.T i) (L34FH.T j) = true :=
      (commPt_iff (penumPt_canon ci) (penumPt_canon cj)).2 (((hui.comp hvj).eq_iff
        (hvj.comp hui)).2 huv)
    have h := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kPair i hi) j hj
    rw [orB_iff, notB_iff, hc] at h
    rcases h with h | h
    · exact absurd h (by decide)
    obtain ⟨k, hk, hk'⟩ := exists_of_notB_allN h
    have hk2 : andB (memM k (L34FH.T i)) (memM k (L34FH.T j)) = true := by
      cases e : andB (memM k (L34FH.T i)) (memM k (L34FH.T j))
      · rw [e] at hk'
        exact absurd hk' (by decide)
      · rfl
    obtain ⟨m1, m2⟩ := andB_iff.1 hk2
    have mem : ∀ {x : Nat} {g : Equiv.Perm (Fin 42)}, TabRep (unpack 42 6 x) g →
        memM k x = true → g ∈ Subgroup.closure (Ms k) := by
      intro x g hg hm
      obtain ⟨q, hq, hq'⟩ := exists_of_notB_allN hm
      have hb : Nat.beq (L34FM.T k q) x = true := by
        cases e : Nat.beq (L34FM.T k q) x
        · rw [e] at hq'
          exact absurd hq' (by decide)
        · rfl
      obtain ⟨g', hg', hr'⟩ := elt_of (encMs hk) hq
      rw [Nat.eq_of_beq_eq_true hb] at hr'
      rwa [hg.perm_eq hr']
    exact ⟨⟨k, hk⟩, mem hui m1, mem hvj m2⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨j, hj, hx⟩
    change j < (mGens[0]!).size at hj
    change TabRep (mGens[0]!)[j]! x at hx
    have hj2 : j < 2 := by rw [(mrec 0 (by decide)).1.1] at hj; exact hj
    obtain ⟨b, h⟩ := andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kS j hj2)
    obtain ⟨g, hgS, hgr⟩ := gen_of encS b h
    rw [← ((mrec 0 (by decide)).1.2 j hj2).1] at hgr
    rw [hx.perm_eq hgr]
    exact hgS
  · rintro ⟨k, hk⟩ hk0
    have hk1 : k ≠ 0 := fun h => hk0 (Fin.ext h)
    obtain ⟨kk, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk1
    exact fix_gen (by omega)

end CertificateChecks.KernelLC.L34Fix

end
