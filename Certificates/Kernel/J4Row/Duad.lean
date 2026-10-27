module

public import Certificates.Kernel.J4Row.Checks
public import Certificates.Kernel.SporSch.Mathieu.M24Facts
public import CFSG.Certificates.Kernel.J4Row.Sound
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import CFSG.RankThree.Native.FiveKit
public import CFSG.Sporadic.Schreier.M24
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Data
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Data.Kernel.J4Q.MatChk

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Row

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Certificates
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.KS.SporSch.MOC
  CFSG.Sporadic.Schreier
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4 (duadSwap)

local notation "R31" => CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4.row31
local notation "R43" => CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4.row43
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.M24OC (chainQ szOK')

theorem andT {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  rw [Bool.and_eq_true] at h
  exact h

theorem m24Binds :
    Binds 24 5 M24Q.S 11 7 M24Q.BP (strongArr 24 5 11 M24Q.S) (baseArr 5 7 M24Q.BP) :=
  binds_of chainQ

theorem m24Perm :
    allN 11 (fun j => permOK 24 5 (mask 5) (24 * 5) (M24Q.S j) (M24Q.SI j)) = true :=
  (Orb.head_facts chainQ.2.2.2.2.2.1).1

theorem m24Levels : LevelsOK 24 5 M24Q.S M24Q.SI M24Q.LR M24Q.TR M24Q.TRI 11 7 M24Q.BP :=
  chainQ.2.2.2.2.2.2.1

theorem m24Arrays : ChainArrays m24Certificate ((strongArr 24 5 11 M24Q.S).extract 0 2)
      (strongArr 24 5 11 M24Q.S) (baseArr 5 7 M24Q.BP)
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 m24Words) ∧
    rawChainOK 24 ((strongArr 24 5 11 M24Q.S).extract 0 2) (strongArr 24 5 11 M24Q.S)
      (baseArr 5 7 M24Q.BP) (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 m24Words) 1 = true :=
  chainK_arrays (by decide) (by decide) chainQ

theorem mem_M24_of {f : ℕ} (hf : inM24 f = true) {G : Equiv.Perm (Fin 24)}
    (hG : Rep 24 (unpack 24 5 f) G) : G ∈ CFSG.Blueprint.NativeSporadic.M24 := by
  unfold inM24 at hf
  obtain ⟨h12, h3⟩ := andT hf
  obtain ⟨h1, h2⟩ := andT h12
  have hs := siftK_soundR m24Binds m24Perm m24Levels rfl (Nat.eq_of_beq_eq_true h1) h2 h3
  rw [← m24Certificate_originalSubgroup]
  exact mem_of_siftA m24Arrays.1 m24Arrays.2 hG hs

theorem rep_permB {f : ℕ} (hf : permB 24 5 f = true) :
    Rep 24 (unpack 24 5 f) (permOfArr 24 (unpack 24 5 f)) :=
  rep_of_validA (validA_of hf)

theorem rep_cm {p q : ℕ} (hp : permB 24 5 p = true) (hq : permB 24 5 q = true)
    {P Q : Equiv.Perm (Fin 24)} (hP : Rep 24 (unpack 24 5 p) P) (hQ : Rep 24 (unpack 24 5 q) Q) :
    Rep 24 (unpack 24 5 (cm 24 5 p q)) (P * Q) := by
  rw [cm, ← comp_unpack' szOK' hp hq]
  exact rep_compA hP hQ

theorem eq_of_cm {p q r s : ℕ} (hp : permB 24 5 p = true) (hq : permB 24 5 q = true)
    (hr : permB 24 5 r = true) (hs : permB 24 5 s = true) {P Q R S : Equiv.Perm (Fin 24)}
    (hP : Rep 24 (unpack 24 5 p) P) (hQ : Rep 24 (unpack 24 5 q) Q)
    (hR : Rep 24 (unpack 24 5 r) R) (hS : Rep 24 (unpack 24 5 s) S)
    (h : cm 24 5 p q = cm 24 5 r s) : P * Q = R * S := by
  have h1 := rep_cm hp hq hP hQ
  rw [h] at h1
  exact Rep.unique h1 (rep_cm hr hs hR hS)

theorem card_duad {π : Equiv.Perm (Fin 24)} {x g X o a b : ℕ} {rels : List (ℕ × ℕ × ℕ)}
    {E : List ℕ} (hx : Rep 24 (unpack 24 5 x) (π * duadSwap)) (ha : (π * duadSwap) ^ a = π)
    (hb : (π * duadSwap) ^ b = duadSwap) (hxK : xK x g X = true)
    (hr : relsK 24 5 o M24Q.BP X 7 rels = true) (he : elK X E = true)
    (ht : tailK X rels E = true) :
    Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 // (σ : Equiv.Perm (Fin 24)) * π = π * σ ∧
        (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} = E.length := by
  classical
  unfold xK at hxK
  obtain ⟨h1, hgM⟩ := andT hxK
  obtain ⟨h1, hgX⟩ := andT h1
  obtain ⟨h1, hXp⟩ := andT h1
  obtain ⟨hxp, hgp⟩ := andT h1
  have rg := rep_permB hgp
  have rX := rep_permB hXp
  have hgM24 := mem_M24_of hgM rg
  unfold elK at he
  obtain ⟨hEall, hEd⟩ := andT he
  have hEm : ∀ c ∈ E, permB 24 5 c = true ∧ cm 24 5 c X = cm 24 5 X c ∧ inM24 c = true := by
    intro c hc
    obtain ⟨h1, h3⟩ := andT (CFSG.KC.J4Row.allR_mem hEall c hc)
    obtain ⟨h1, h2⟩ := andT h1
    exact ⟨h1, Nat.eq_of_beq_eq_true h2, h3⟩
  have hcx : ∀ σ : Equiv.Perm (Fin 24),
      (σ * π = π * σ ∧ σ * duadSwap = duadSwap * σ) ↔ σ * (π * duadSwap) = π * duadSwap * σ := by
    intro σ
    constructor
    · rintro ⟨h1, h2⟩
      rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
    · intro h
      have hc : Commute σ (π * duadSwap) := h
      have e1 := (hc.pow_right a).eq
      have e2 := (hc.pow_right b).eq
      rw [ha] at e1
      rw [hb] at e2
      exact ⟨e1, e2⟩
  have hbc : m24Certificate.baseCount = 7 := by
    rw [← m24Arrays.1.base_size]
    exact m24Binds.2.2.2.2.2.1
  have hbp : ∀ t < 7, (baseArr 5 7 M24Q.BP)[t]! = pg 5 (mask 5) M24Q.BP t :=
    m24Binds.2.2.2.2.2.2
  have hbn : ∀ t < 7, pg 5 (mask 5) M24Q.BP t < 24 := fun t ht => by
    rw [← hbp t ht]
    exact Orb.base_lt_of_levels m24Binds m24Levels t ht
  have hrel := relsOKP_spec (relsOKP_of szOK' m24Binds.2.2.2.2.2.1 hbp hbn hXp hr)
  have hEp : ∀ e < CFSG.KC.J4Row.lenR E, permB 24 5 (CFSG.KC.J4Q.getN 0 E e) = true := by
    intro e he
    rw [CFSG.KC.J4Row.lenR_eq] at he
    rw [CFSG.KC.J4Row.getN_getD, List.getD_eq_getElem _ _ he]
    exact (hEm _ (List.getElem_mem he)).1
  unfold tailK at ht
  have htl := ptailK_sound m24Binds m24Perm m24Levels (x := unpack 24 5 X) rfl hXp
    (powPA_get szOK' hXp) (fun r hr' => (hrel r hr').1) (E := (List.range (CFSG.KC.J4Row.lenR E)).map
      fun e => unpack 24 5 (CFSG.KC.J4Q.getN 0 E e)) rfl hEp (by norm_num) (Orb.allN_iff.1 ht)
  have htl' : ptailOK 24 (rawLevels 24 (strongArr 24 5 11 M24Q.S) (baseArr 5 7 M24Q.BP))
      (baseArr 5 7 M24Q.BP) (unpack 24 5 X) (powPA o 24 (unpack 24 5 X)) rels
      ((List.range (CFSG.KC.J4Row.lenR E)).map fun e => unpack 24 5 (CFSG.KC.J4Q.getN 0 E e))
      m24Certificate.baseCount 0 (idA 24) = true := by
    rw [hbc]
    exact htl
  have hQ := (validSchreier_of_chainOK m24Arrays.1 (by norm_num) m24Arrays.2).1
  have hcent : ∀ ρ ∈ Subgroup.centralizer {permOfArr 24 (unpack 24 5 X)} ⊓
      m24Certificate.originalSubgroup, ∃ e ∈ (List.range (CFSG.KC.J4Row.lenR E)).map
        (fun e => unpack 24 5 (CFSG.KC.J4Q.getN 0 E e)), Rep 24 e ρ := fun ρ hρ =>
    centralizer_subset_of_ptailOK m24Arrays.1 (chainCheckFacts m24Arrays.2) hQ rX (rep_powPA rX)
      hrel htl' hρ
  have hgXe : permOfArr 24 (unpack 24 5 g) * permOfArr 24 (unpack 24 5 X) =
      π * duadSwap * permOfArr 24 (unpack 24 5 g) :=
    eq_of_cm hgp hXp hxp hgp rg rX hx rg (Nat.eq_of_beq_eq_true hgX)
  set gh := permOfArr 24 (unpack 24 5 g) with hgh
  set Xh := permOfArr 24 (unpack 24 5 X) with hXh
  have hX' : Xh = gh⁻¹ * (π * duadSwap) * gh := by
    rw [mul_assoc, ← hgXe, ← mul_assoc, inv_mul_cancel, one_mul]
  have hx' : π * duadSwap = gh * Xh * gh⁻¹ := by
    rw [hX']
    group
  set L := E.map fun c => gh * permOfArr 24 (unpack 24 5 c) * gh⁻¹ with hL
  have hLnd : L.Nodup := by
    refine List.Nodup.map_on ?_ (CFSG.KC.J4Row.distinctK_nodup hEd)
    intro c hc d hd hcd
    have e := mul_left_cancel (mul_right_cancel hcd)
    have hcp := (hEm c hc).1
    have hdp := (hEm d hd).1
    have h := (eqA_iff (rep_permB hcp) (rep_permB hdp)).2 e
    rw [eqA_unpack' szOK' hcp hdp] at h
    exact Nat.eq_of_beq_eq_true h
  have hiff : ∀ σ : Equiv.Perm (Fin 24), (σ ∈ CFSG.Blueprint.NativeSporadic.M24 ∧
      σ * π = π * σ ∧ σ * duadSwap = duadSwap * σ) ↔ σ ∈ L := by
    intro σ
    constructor
    · rintro ⟨hσ, hσc⟩
      have h := (hcx σ).1 hσc
      have hρM : gh⁻¹ * σ * gh ∈ m24Certificate.originalSubgroup := by
        rw [m24Certificate_originalSubgroup]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgM24) hσ) hgM24
      have hρc : gh⁻¹ * σ * gh * Xh = Xh * (gh⁻¹ * σ * gh) := by
        rw [hX']
        calc gh⁻¹ * σ * gh * (gh⁻¹ * (π * duadSwap) * gh) = gh⁻¹ * (σ * (π * duadSwap)) * gh := by
              group
          _ = gh⁻¹ * (π * duadSwap * σ) * gh := by rw [h]
          _ = gh⁻¹ * (π * duadSwap) * gh * (gh⁻¹ * σ * gh) := by group
      obtain ⟨e, he, hre⟩ := hcent (gh⁻¹ * σ * gh)
        (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hρc, hρM⟩)
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
      rw [List.mem_range, CFSG.KC.J4Row.lenR_eq] at hi
      have hcE : CFSG.KC.J4Q.getN 0 E i ∈ E := by
        rw [CFSG.KC.J4Row.getN_getD, List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      have e2 := Rep.unique hre (rep_permB (hEm _ hcE).1)
      refine List.mem_map.2 ⟨_, hcE, ?_⟩
      beta_reduce
      rw [← e2]
      group
    · intro hσ
      obtain ⟨c, hc, hcσ⟩ := List.mem_map.1 hσ
      rw [← hcσ]
      beta_reduce
      obtain ⟨hcp, hcX, hcM⟩ := hEm c hc
      have rc := rep_permB hcp
      have hcomm : permOfArr 24 (unpack 24 5 c) * Xh = Xh * permOfArr 24 (unpack 24 5 c) :=
        eq_of_cm hcp hXp hXp hcp rc rX rX rc hcX
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgM24 (mem_M24_of hcM rc))
        (Subgroup.inv_mem _ hgM24), (hcx _).2 ?_⟩
      rw [hx']
      calc gh * permOfArr 24 (unpack 24 5 c) * gh⁻¹ * (gh * Xh * gh⁻¹) =
            gh * (permOfArr 24 (unpack 24 5 c) * Xh) * gh⁻¹ := by group
        _ = gh * (Xh * permOfArr 24 (unpack 24 5 c)) * gh⁻¹ := by rw [hcomm]
        _ = gh * Xh * gh⁻¹ * (gh * permOfArr 24 (unpack 24 5 c) * gh⁻¹) := by group
  have e1 : {σ : CFSG.Blueprint.NativeSporadic.M24 // (σ : Equiv.Perm (Fin 24)) * π = π * σ ∧
      (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} ≃ ↥L.toFinset :=
    { toFun := fun s => ⟨s.1.1, List.mem_toFinset.2 ((hiff _).1 ⟨s.1.2, s.2⟩)⟩
      invFun := fun s => ⟨⟨s.1, ((hiff _).2 (List.mem_toFinset.1 s.2)).1⟩,
        ((hiff _).2 (List.mem_toFinset.1 s.2)).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e1, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hLnd, hL,
    List.length_map]

theorem rep_x31 :
    CFSG.Monster.B.Co2.Rep 24 (unpack 24 5 CFSG.KD.J4Row.r31x) ((R31).piPerm * duadSwap) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem rep_x43 :
    CFSG.Monster.B.Co2.Rep 24 (unpack 24 5 CFSG.KD.J4Row.r43x) ((R43).piPerm * duadSwap) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide +kernel

theorem pow31a : ((R31).piPerm * duadSwap) ^ 6 = (R31).piPerm := by decide +kernel

theorem pow31b : ((R31).piPerm * duadSwap) ^ 5 = duadSwap := by decide +kernel

theorem pow43a : ((R43).piPerm * duadSwap) ^ 8 = (R43).piPerm := by decide +kernel

theorem pow43b : ((R43).piPerm * duadSwap) ^ 7 = duadSwap := by decide +kernel

theorem len31 : CFSG.KD.J4Row.r31E.length = 10 := by decide +kernel

theorem len43 : CFSG.KD.J4Row.r43E.length = 14 := by decide +kernel

theorem card_duad31 :
    Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 //
      (σ : Equiv.Perm (Fin 24)) * (R31).piPerm = (R31).piPerm * σ ∧
        (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} = 10 :=
  (card_duad rep_x31 pow31a pow31b x31 rels31 el31 tail31).trans len31

theorem card_duad43 :
    Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 //
      (σ : Equiv.Perm (Fin 24)) * (R43).piPerm = (R43).piPerm * σ ∧
        (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} = 14 :=
  (card_duad rep_x43 pow43a pow43b x43 rels43 el43 tail43).trans len43

end CertificateChecks.KernelJ4Row

end
