module

public import Certificates.Kernel.O8Frame9490.Glue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8F

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelO8
open CFSG.KC.O8F CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
open CFSG.EvenSmallLie.OmegaEightMinus CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.Misc.PairCount (unpack_get)

theorem testBit_fold (s : Fin 5 → Fin 5) (u j : Nat) : ∀ (l : List (Fin 5)) (a : Nat),
    (l.map s).Nodup →
    (l.foldl (fun acc (i : Fin 5) => if u.testBit i then acc ^^^ 2 ^ (s i : ℕ) else acc) a).testBit j =
      (a.testBit j ^^ l.any (fun (i : Fin 5) => u.testBit i && decide ((s i : ℕ) = j)))
  | [], a, _ => by simp
  | i :: l, a, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.foldl_cons, testBit_fold s u j l _ hn.2, List.any_cons]
    by_cases hu : u.testBit i = true
    · rw [if_pos hu, Nat.testBit_xor, Nat.testBit_two_pow, hu, Bool.true_and]
      by_cases hj : (s i : ℕ) = j
      · have : l.any (fun (k : Fin 5) => u.testBit k && decide ((s k : ℕ) = j)) = false := by
          rw [List.any_eq_false]
          intro k hk hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          exact hn.1 (List.mem_map.2 ⟨k, hk, Fin.ext (hc.2.trans hj.symm)⟩)
        simp [hj, this]
      · simp [hj]
    · simp [hu]

theorem testBit_permBits (σ : Equiv.Perm (Fin 5)) (u j : Nat) :
    (permBits σ u).testBit j =
      (List.finRange 5).any (fun (i : Fin 5) => u.testBit i && decide ((σ i : ℕ) = j)) := by
  unfold permBits
  rw [testBit_fold σ u j _ 0 ((List.nodup_finRange 5).map σ.injective)]
  simp

theorem permBits_mul (σ τ : Equiv.Perm (Fin 5)) (u : Nat) :
    permBits ⇑(σ * τ) u = permBits σ (permBits τ u) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_permBits, testBit_permBits]
  simp only [testBit_permBits]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, hj⟩
    exact ⟨τ k, ⟨k, hk, rfl⟩, hj⟩
  · rintro ⟨i, ⟨k, hk, hki⟩, hj⟩
    refine ⟨k, hk, ?_⟩
    have e : τ k = i := Fin.ext hki
    change ((σ (τ k) : Fin 5) : ℕ) = j
    rw [e]
    exact hj

@[expose] def tup (σ : Equiv.Perm (Fin 5)) : List Nat := List.ofFn fun i => (σ i : Nat)

theorem tup_mem (σ : Equiv.Perm (Fin 5)) : tup σ ∈ (List.range 5).permutations' := by
  rw [List.mem_permutations']
  have e : tup σ = ((List.finRange 5).map σ).map Fin.val := by
    rw [tup, List.ofFn_eq_map, List.map_map]
    rfl
  have e2 : (List.finRange 5).map Fin.val = List.range 5 := by decide
  rw [e, ← e2]
  exact (Equiv.Perm.map_finRange_perm σ).map Fin.val

theorem sign_eq (σ : Equiv.Perm (Fin 5)) : ((Equiv.Perm.sign σ : Int)) = sgnT (tup σ) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  have h0 : Finset.Ioi (0:Fin 5) = {1,2,3,4} := by decide
  have h1 : Finset.Ioi (1:Fin 5) = {2,3,4} := by decide
  have h2 : Finset.Ioi (2:Fin 5) = {3,4} := by decide
  have h3 : Finset.Ioi (3:Fin 5) = {4} := by decide
  have h4 : Finset.Ioi (4:Fin 5) = ∅ := by decide
  have e : sgnT (tup σ) = (if (σ 0 : Nat) < σ 1 then 1 else -1) *
      ((if (σ 0 : Nat) < σ 2 then 1 else -1) *
      ((if (σ 0 : Nat) < σ 3 then 1 else -1) * ((if (σ 0 : Nat) < σ 4 then 1 else -1) *
      ((if (σ 1 : Nat) < σ 2 then 1 else -1) * ((if (σ 1 : Nat) < σ 3 then 1 else -1) *
      ((if (σ 1 : Nat) < σ 4 then 1 else -1) * ((if (σ 2 : Nat) < σ 3 then 1 else -1) *
      ((if (σ 2 : Nat) < σ 4 then 1 else -1) * ((if (σ 3 : Nat) < σ 4 then 1 else -1) *
        1))))))))) := rfl
  rw [e]
  simp only [Fin.prod_univ_five, h0, h1, h2, h3, h4, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty, Units.val_mul, Units.val_one,
    apply_ite Units.val, Units.val_neg, Fin.lt_iff_val_lt_val]
  simp only [Finset.prod_insert (show (1 : Fin 5) ∉ ({2, 3, 4} : Finset (Fin 5)) by decide),
    Finset.prod_insert (show (2 : Fin 5) ∉ ({3, 4} : Finset (Fin 5)) by decide),
    Finset.prod_pair (show (3 : Fin 5) ≠ 4 by decide), Units.val_mul, apply_ite Units.val,
    Units.val_one, Units.val_neg]
  ring

theorem psi_ok (σ : Equiv.Perm (Fin 5)) : psiOK (tup σ) = true :=
  List.all_eq_true.1 kPsi _ (tup_mem σ)

theorem psi_facts (σ : Equiv.Perm (Fin 5)) :
    fnLtK NSM (psiCodeT (tup σ)) = true ∧ okK (psiK (tup σ)) = true ∧
      Nat.beq (pcM (psiK (tup σ)) (BK 0)) (pcM (BK 0) (psiK (tup σ))) = true ∧
      bIf(decide (sgnT (tup σ) = 1), siftOm (psiK (tup σ)), true) = true ∧
      ∀ i < 136, rtK (tup σ) i = true := by
  have h := psi_ok σ
  unfold psiOK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h2⟩ := band h
  obtain ⟨h2, h3⟩ := band h2
  obtain ⟨h3, h4⟩ := band h3
  obtain ⟨h4, h5⟩ := band h4
  exact ⟨h1, h2, h3, h4, allN_spec h5⟩

theorem psiArr_eq (σ : Equiv.Perm (Fin 5)) : psiArr σ = unpack 136 8 (psiK (tup σ)) :=
  fnK_eq (psi_facts σ).1

theorem rt_facts (σ : Equiv.Perm (Fin 5)) {i : Nat} (hi : i < 136) :
    nsIdx[psiCode σ nsArr[i]!]! < 136 ∧ nsArr[nsIdx[psiCode σ nsArr[i]!]!]! = psiCode σ nsArr[i]! ∧
      psiCoord (psiCode σ nsArr[i]!) = permBits σ (psiCoord nsArr[i]!) := by
  have h := (psi_facts σ).2.2.2.2 i hi
  have hl : psiCodeT (tup σ) (pg 8 255 NSM i) < 256 := by
    have := (CFSG.KC.O8.PA.ctAllN_iff).1 (psi_facts σ).1 i hi
    rwa [Nat.blt_eq, fget_pg8] at this
  unfold rtK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h2⟩ := band h
  obtain ⟨h2, h3⟩ := band h2
  simp only [fget_pg8] at h1 h2 h3
  rw [← ns_bindM i hi] at h1 h2 h3 hl
  rw [← ni_bindM _ hl] at h1 h2
  have hn : nsIdx[psiCodeT (tup σ) nsArr[i]!]! < 136 := Nat.blt_eq.mp h1
  rw [← ns_bindM _ hn] at h2
  exact ⟨hn, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem psiCode_mul (σ τ : Equiv.Perm (Fin 5)) {i : Nat} (hi : i < 136) :
    psiCode ⇑(σ * τ) nsArr[i]! = psiCode σ (psiCode τ nsArr[i]!) := by
  have hc := (rt_facts τ hi).2.2
  conv_rhs => rw [psiCode, hc]
  rw [psiCode, psiCode, permBits_mul, Nat.xor_assoc (nsArr[i]! ^^^ psiIota (psiCoord nsArr[i]!)),
    Nat.xor_self, Nat.xor_zero]

theorem psiArr_get (σ : Equiv.Perm (Fin 5)) {k : Nat} (hk : k < 136) :
    (psiArr σ)[k]! = nsIdx[psiCode σ nsArr[k]!]! := by
  unfold psiArr
  exact getElem!_ofFn136 hk

theorem psiArr_mul (σ τ : Equiv.Perm (Fin 5)) :
    psiArr (σ * τ) = compA 136 (psiArr σ) (psiArr τ) := by
  have e : psiArr (σ * τ) =
      Array.ofFn (n := 136) (fun j => nsIdx[psiCode ⇑(σ * τ) nsArr[j.val]!]!) := rfl
  rw [e]
  unfold compA
  refine congrArg (Array.ofFn (n := 136)) (funext fun j => ?_)
  rw [psiArr_get τ j.2, psiArr_get σ (rt_facts τ j.2).1, (rt_facts τ j.2).2.1,
    psiCode_mul σ τ j.2]

theorem psi_k : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame.psiCheck = true := by
  unfold CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame.psiCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨fun σ τ => ?_, fun σ => ?_⟩, fun σ => ?_⟩, fun σ hσ => ?_⟩, ?_⟩
  · rw [psiArr_mul]
    exact eqA_refl136 _
  · rw [psiArr_eq]
    exact isInvA_ofM (okK_iff (psi_facts σ).2.1).2.1
  · have hp := (okK_iff (psi_facts σ).2.1).1
    have hb := (okK_iff (bk_ok (by norm_num : 0 < 3))).1
    rw [psiArr_eq, beta_eq (by norm_num), compA_pcM hp hb, compA_pcM hb hp,
      eqA_pcM (cn_pcM hp hb) (cn_pcM hb hp)]
    exact (psi_facts σ).2.2.1
  · have hs : sgnT (tup σ) = 1 := by rw [← sign_eq, hσ]; rfl
    have h := (psi_facts σ).2.2.2.1
    rw [hs] at h
    rw [psiArr_eq]
    exact siftOm_sound (psi_facts σ).2.1 h
  · have e : tup (Equiv.swap 0 1 * Equiv.swap 1 2) = [1, 2, 0, 3, 4] := by decide
    have hp := (okK_iff (psi_facts (Equiv.swap 0 1 * Equiv.swap 1 2)).2.1).1
    rw [psiArr_eq, idA_eq, eqA_pcM hp cn_id, e]
    have := kSwap
    simpa using this

end CertificateChecks.KernelO8F

end
