
module

public import Certificates.Kernel.SporSch.Ru.Q7305K
import Certificates.Kernel.SporSch.Ru.Q7307
import Certificates.Kernel.SporSch.Ru.Iso7047
import Certificates.Kernel.SporSch.Ru.G2Ru7164
import Certificates.Kernel.SporSch.Ru.JFacts
import CFSG.Certificates.Kernel.SporSch.OrbLabelsSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Q7305

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164
  CertificateChecks.KernelSporSch.Q7307
  CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CFSG.KC.BfsPin

theorem eg_eq {i : Nat} (hi : i < 2) : ruEGArr i = unpack 4060 12 (Q7305E.F i) := by
  rw [ruEGArr, Q7305E.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound Q7305E.all i hi

theorem fr_eq {i : Nat} (hi : i < 2) : ruFrobArr i = unpack 4060 12 (FR i) := by
  rw [ruFrobArr, Q7305F.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound Q7305F.all i hi

theorem elab_get {y : Nat} (hy : y < 4060) : ruELab[y]! = ELf y := by
  have hs : ruEGArrs.size = 2 := by simp [ruEGArrs]
  have hg : ∀ k < 2, ∀ x < 4060, ga ruEGArrs k x = gE k x := fun k hk x hx => by
    unfold ga ruEGArrs
    rw [getElem!_ofFn_of_lt _ hk]
    change (ruEGArr k)[x]! = _
    rw [eg_eq hk, CFSG.KC.BfsPin.unpack_get' hx]
    rfl
  exact (orbLabels_of_K hs hg kOrbE).2 y hy

theorem elab_lt {y : Nat} (hy : y < 4060) : ELf y < 9 := by
  have := allN_spec kLt y hy
  simpa using this

theorem tig0_eq : ruTIG0 = unpack 4060 12 TG := by
  have hP : ∀ j < 2, P (Af j) := fun j hj => by
    interval_cases j
    · exact PP_of_permOK hsz kPerm0
    · exact PP_of_permOK hsz kPerm1
  have hS : ∀ j < 2, ruGensA[j]! = unpack 4060 12 (Af j) := fun j hj => by
    interval_cases j
    · rw [show ruGensA[0]! = ruA0A by simp [ruGensA], a0_eq]
      rfl
    · rw [show ruGensA[1]! = ruA1A by simp [ruGensA], a1_eq]
      rfl
  have hinv : ruGensInvA = ruGensA.map (invCand 4060) := by
    simp [ruGensInvA, ruGensA, ruInv]
  have hw : ∀ l ∈ Iso7047.twK 32 2808, l ≠ 0 ∧ l.natAbs ≤ 2 := fun l hl => by
    have := List.all_eq_true.1 kWordG l hl
    simpa using this
  have e : ruTreeWord 2808 = Iso7047.twK 32 2808 := Iso7047.treeWordAux_eq 32 2808 (by norm_num)
  obtain ⟨h1, h2⟩ := wordA_eq (S := ruGensA) (k := 2) (by simp [ruGensA]) hS hP _ hw
  change invCand 4060 (wordA 4060 ruGensA ruGensInvA (ruTreeWord 2808)) = _
  rw [hinv, e, h1, inv_eq h2]
  rfl

theorem inD_eq {x : Nat} (hx : x < 4060) : ruInD x = Nat.beq (Lf x) (Lf 1) := by
  unfold ruInD
  rw [qlab_get hx, qlab_get (by norm_num), nat_beq]

theorem inS_eq {x : Nat} (hx : x < 4060) : ruInS x = Nat.beq (Lf x) (Lf 2808) := by
  unfold ruInS
  rw [qlab_get hx, show ruG0 = 2808 from rfl, qlab_get (by norm_num), nat_beq]

theorem row_eq {x : Nat} (hx : x < 4060) (ht : fl TG x < 4060) :
    ruRowA ruTIG0 x = Nat.beq (Lf (fl TG x)) (Lf 1) := by
  unfold ruRowA
  rw [tig0_eq, CFSG.KC.BfsPin.unpack_get' hx, qlab_get (by unfold fl at ht; simpa using ht),
    qlab_get (by norm_num), nat_beq]
  rfl

theorem e_get {x : Nat} (hx : x < 4060) : fl TG x < 4060 ∧
    ((Nat.beq (Lf x) (Lf 1) && Nat.beq (Lf (fl TG x)) (Lf 1)) == Nat.beq (ELf x) 2) = true ∧
    ((Nat.beq (Lf x) (Lf 1) && !Nat.beq (Lf (fl TG x)) (Lf 1)) == Nat.beq (ELf x) 1) = true ∧
    ((Nat.beq (Lf x) (Lf 2808) && Nat.beq (Lf (fl TG x)) (Lf 1)) == Nat.beq (ELf x) 3) = true := by
  have h := kE
  rw [Q7307.strictB_eq] at h
  have hp := allN_spec h x hx
  unfold eOK at hp
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hp
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨h2, h3⟩, h4⟩ := h2
  exact ⟨by simpa using h1, h2, h3, h4⟩

theorem sel_eq {p : Nat → Bool} : ∀ xs : List Nat, (∀ x ∈ xs, x < 4060) →
    xs.countP (fun x => p (ELf x)) =
      ∑ l ∈ Finset.range 9, if p l then xs.countP (fun x => Nat.beq (ELf x) l) else 0
  | [], _ => by simp
  | x :: xs, h => by
    have ih := sel_eq (p := p) xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hlt := elab_lt (h x List.mem_cons_self)
    simp only [List.countP_cons, ih]
    have e1 : ∀ l ∈ Finset.range 9, (if p l then
        (xs.countP (fun x => Nat.beq (ELf x) l) + if Nat.beq (ELf x) l = true then 1 else 0) else 0) =
        (if p l then xs.countP (fun x => Nat.beq (ELf x) l) else 0) +
          (if ELf x = l then (if p l then 1 else 0) else 0) := fun l _ => by
      by_cases hp : p l <;> by_cases he : ELf x = l <;> simp [hp, he, Nat.beq_eq]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_ite_eq,
      if_pos (Finset.mem_range.2 hlt)]

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem c7305 :
    ((allLt 4060 fun x => (ruInD x && ruRowA ruTIG0 x) == (ruELab[x]! == 2)) = true ∧
       (allLt 4060 fun x => (ruInD x && !ruRowA ruTIG0 x) == (ruELab[x]! == 1)) = true ∧
       (allLt 4060 fun x => (ruInS x && ruRowA ruTIG0 x) == (ruELab[x]! == 3)) = true ∧
       ruELab[2]! = 2 ∧
       (∀ b : Fin 9 → Bool, selCount 4060 ruELab b = 975 →
         (allLt 4060 fun x => !(bAt b ruELab[x]!) || ruInS x) = true →
         (allLt 4060 fun x => bAt b ruELab[x]! == (ruELab[x]! == 3)) = true))
    ∧ ((allLt 2 fun i => isInvA 4060 (ruFrobArr i) (invCand 4060 (ruFrobArr i)) &&
         ruSift 4060 (ruField4060 3) ruJoinBase (ruFrobArr i) && (ruFrobArr i)[0]! == 0 &&
         (ruFrobArr i)[ruG0]! == ruG0 && (ruFrobArr i)[2]! == 2) = true ∧
       eqA 4060 (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 0) 5) (idA 4060) = true ∧
       eqA 4060 (ruFrobArr 0) (idA 4060) = false ∧
       eqA 4060 (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 1) 4) (idA 4060) = true ∧
       eqA 4060 (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 1) 2) (idA 4060) = false ∧
       eqA 4060 (ruConjArr (ruFrobArr 1) (ruFrobArr 0))
         (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 0) 2) = true) := by
  have hF : ∀ i < 2, P (FR i) := fun i hi => by
    interval_cases i
    · exact PP_of_permOK hsz ((bAnd_iff _ _).1 kF0).1
    · exact PP_of_permOK hsz ((bAnd_iff _ _).1 kF1).1
  obtain ⟨w0, w1, w2, s0, s1, s2⟩ : ELf 0 = 0 ∧ ELf 1 = 1 ∧ ELf 2 = 2 ∧ Lf 0 ≠ Lf 2808 ∧
      Lf 1 ≠ Lf 2808 ∧ Lf 2 ≠ Lf 2808 := by
    have h := kWit
    simp only [bAnd_iff, Nat.beq_eq] at h
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
    refine ⟨h0, h1, h2, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [e] at h3
      simp at h3
    · rw [e] at h4
      simp at h4
    · rw [e] at h5
      simp at h5
  refine ⟨⟨?_, ?_, ?_, by rw [elab_get (by norm_num), w2], ?_⟩, ?_⟩
  · refine CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_
    obtain ⟨ht, h2, -, -⟩ := e_get hx
    rw [inD_eq hx, row_eq hx ht, elab_get hx, nat_beq]
    exact h2
  · refine CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_
    obtain ⟨ht, -, h3, -⟩ := e_get hx
    rw [inD_eq hx, row_eq hx ht, elab_get hx, nat_beq]
    exact h3
  · refine CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_
    obtain ⟨ht, -, -, h4⟩ := e_get hx
    rw [inS_eq hx, row_eq hx ht, elab_get hx, nat_beq]
    exact h4
  · intro b hsel hall
    have hall' := CFSG.Monster.B.Co2.allLt_iff.1 hall
    have hb : ∀ x < 3, bAt b x = false := fun x hx => by
      have h := hall' x (by omega)
      rw [elab_get (by omega), inS_eq (by omega)] at h
      interval_cases x
      · rw [w0] at h
        simpa [Nat.beq_eq, s0] using h
      · rw [w1] at h
        simpa [Nat.beq_eq, s1] using h
      · rw [w2] at h
        simpa [Nat.beq_eq, s2] using h
    have hs : selCount 4060 ruELab b = (List.range 4060).countP (fun x => bAt b (ELf x)) := by
      unfold selCount
      apply List.countP_congr
      intro x hx
      rw [elab_get (List.mem_range.1 hx)]
    rw [hs, sel_eq (p := bAt b) _ (fun x hx => List.mem_range.1 hx)] at hsel
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsel
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := kCnt
    unfold cnt at c0 c1 c2 c3 c4 c5 c6 c7 c8
    rw [c0, c1, c2, c3, c4, c5, c6, c7, c8, hb 0 (by omega), hb 1 (by omega),
      hb 2 (by omega)] at hsel
    have key : bAt b 3 = true ∧ bAt b 4 = false ∧ bAt b 5 = false ∧ bAt b 6 = false ∧
        bAt b 7 = false ∧ bAt b 8 = false := by
      revert hsel
      generalize bAt b 3 = b3
      generalize bAt b 4 = b4
      generalize bAt b 5 = b5
      generalize bAt b 6 = b6
      generalize bAt b 7 = b7
      generalize bAt b 8 = b8
      decide +revert
    refine CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_
    rw [elab_get hx]
    have hlt := elab_lt hx
    generalize ELf x = e at hlt ⊢
    obtain ⟨k3, k4, k5, k6, k7, k8⟩ := key
    interval_cases e <;> simp [hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), k3, k4, k5, k6,
      k7, k8]
  · obtain ⟨p0, p1, p2, p3, p4⟩ : powK (FR 0) 5 = pid ∧ FR 0 ≠ pid ∧ powK (FR 1) 4 = pid ∧
        powK (FR 1) 2 ≠ pid ∧ conjK (FR 1) (FR 0) = powK (FR 0) 2 := by
      have h := kPow
      simp only [bAnd_iff, Nat.beq_eq] at h
      obtain ⟨h0, h1, h2, h3, h4⟩ := h
      refine ⟨h0, fun e => ?_, h2, fun e => ?_, h4⟩
      · rw [e] at h1
        simp at h1
      · rw [e] at h3
        simp at h3
    have e0 := fr_eq (i := 0) (by omega)
    have e1 := fr_eq (i := 1) (by omega)
    refine ⟨CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h : fOK i = true := by
        interval_cases i
        exacts [kF0, kF1]
      unfold fOK at h
      simp only [bAnd_iff] at h
      obtain ⟨hperm, hhi, hrange, hsift, h0, hg0, h2⟩ := h
      have hR := fr_eq hi
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨(inv_of hR hperm).2, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact siftK_soundR RuJ.bindsJ RuJ.permJ RuJS.hl hR (Nat.eq_of_beq_eq_true hhi) hrange hsift
      · rw [hR, CFSG.KC.BfsPin.unpack_get' (by norm_num)]
        exact Nat.eq_of_beq_eq_true h0
      · rw [hR, show ruG0 = 2808 from rfl, CFSG.KC.BfsPin.unpack_get' (by norm_num)]
        exact Nat.eq_of_beq_eq_true hg0
      · rw [hR, CFSG.KC.BfsPin.unpack_get' (by norm_num)]
        exact Nat.eq_of_beq_eq_true h2
    · rw [e0, (powA_eq (hF 0 (by omega)) 5).1, G2Ru7164.id_eq, eq_eq (powA_eq (hF 0 (by omega)) 5).2 P_pid, p0]
      exact Nat.beq_refl _
    · rw [e0, G2Ru7164.id_eq, eq_eq (hF 0 (by omega)) P_pid]
      cases h : Nat.beq (FR 0) pid
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) p1
    · rw [e1, (powA_eq (hF 1 (by omega)) 4).1, G2Ru7164.id_eq, eq_eq (powA_eq (hF 1 (by omega)) 4).2 P_pid, p2]
      exact Nat.beq_refl _
    · rw [e1, (powA_eq (hF 1 (by omega)) 2).1, G2Ru7164.id_eq, eq_eq (powA_eq (hF 1 (by omega)) 2).2 P_pid]
      cases h : Nat.beq (powK (FR 1) 2) pid
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) p3
    · unfold ruConjArr
      rw [e0, e1, (conj_eq (hF 1 (by omega)) (hF 0 (by omega))).1, (powA_eq (hF 0 (by omega)) 2).1,
        eq_eq (conj_eq (hF 1 (by omega)) (hF 0 (by omega))).2 (powA_eq (hF 0 (by omega)) 2).2, p4]
      exact Nat.beq_refl _

end CertificateChecks.KernelSporSch.Q7305

end
