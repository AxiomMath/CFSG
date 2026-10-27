module

public import Certificates.Kernel.SporSch.Tits.T614A
public import Certificates.Kernel.SporSch.Tits.T614CJ
public import Certificates.Kernel.SporSch.Tits.T614SS
public import Certificates.Kernel.SporSch.Tits.T614OU
public import Certificates.Kernel.SporSch.Tits.T614N
public import CFSG.Certificates.Kernel.SporSch.TitsEnum5QSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Schreier.TitsPair
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.T614

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Quasithin.H13.Tits614
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel

theorem strictB_eq7195 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem exists_of_allN_false {n : Nat} {f : Nat → Bool} (h : allN n f = false) :
    ∃ i < n, f i = false := by
  by_contra hc
  have : allN n f = true := allN_of_forall fun i hi => by
    cases hf : f i
    · exact absurd ⟨i, hi, hf⟩ hc
    · rfl
  rw [h] at this
  exact absurd this (by decide)

theorem cjp_check_k : all5 1755 titsSLevels (fun a => !(inJ a) ||
    !(eqA 1755 (compA 1755 a pArr) (compA 1755 pArr a)) || eqA 1755 a (idA 1755) ||
    eqA 1755 a titsZArr) = true := by
  refine all5K_sound bindsS permS TitsS.hl (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 _ h => ?_) T614CJ.all
  rw [p_eq, ← commPts_sound c0 c1 c2 c3 c4 cP, id_eq, ← eqPts_sound c0 c1 c2 c3 c4 canId, z_eq,
    ← eqPts_sound c0 c1 c2 c3 c4 canonZ]
  change bIf(commPts 1755 11 (mask 11) T614P t0 t1 t2 t3 t4,
    bIf(eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4, true,
      eqPts 1755 11 (mask 11) TitsZ t0 t1 t2 t3 t4), true) = true at h
  cases hc : commPts 1755 11 (mask 11) T614P t0 t1 t2 t3 t4
  · simp
  · rw [hc] at h
    cases he : eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4
    · rw [he] at h
      simp [h]
    · simp

theorem kLab : allN 3 (fun i => allN 1755 (fun x =>
    Nat.beq (labT (pg 11 (mask 11) (TitsS.S i) x)) (labT x))) = true := by quickRfl

theorem labS_gen {i : Nat} (hi : i < 3) (q : Fin 1755) :
    labT ((titsSGen i q : Fin 1755) : Nat) = labT q := by
  have e : ((titsSGen i q : Fin 1755) : Nat) = pg 11 (mask 11) (TitsS.S i) q := by
    rw [← (titsSGen_rep hi) q, s_get (by omega), unpack_get q.2]
  rw [e]
  exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec kLab i hi) q q.2)

theorem lab_inv {σ : Equiv.Perm (Fin 1755)} (hσ : σ ∈ titsS) :
    ∀ q : Fin 1755, labT ((σ q : Fin 1755) : Nat) = labT q := by
  rw [titsS_eq_closure] at hσ
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact labS_gen i.2
  | one => exact fun q => rfl
  | mul x y _ _ hx hy => exact fun q => by rw [Equiv.Perm.mul_apply, hx, hy]
  | inv x _ hx =>
    intro q
    have h := hx (x⁻¹ q)
    have hq : x (x⁻¹ q) = q := by simp
    rw [hq] at h
    exact h.symm

theorem piK : Nat.beq T614PI (pinv T614P) = true := by quickRfl

theorem ssp_check_k : all5 1755 titsSLevels (fun a =>
    !(inS (compA 1755 (compA 1755 (invCand 1755 pArr) a) pArr)) || inJ a) = true := by
  refine all5K_sound bindsS permS TitsS.hl (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 hinv h => ?_)
    T614SS.all
  have cx : C (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) := cc (cc (cc (cc c0 c1) c2) c3) c4
  change bIf(allN 2 (labEq t0 t1 t2 t3 t4), sfJ (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4),
    true) = true at h
  show (!(inS (compA 1755 (compA 1755 (invCand 1755 pArr)
      (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) pArr)) ||
    inJ (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) = true
  cases hl : allN 2 (labEq t0 t1 t2 t3 t4)
  · have hS : inS (compA 1755 (compA 1755 (invCand 1755 pArr)
        (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) pArr) = false := by
      cases hs : inS (compA 1755 (compA 1755 (invCand 1755 pArr)
          (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) pArr)
      · rfl
      · exfalso
        have hA := (rep_permOfArr hinv).1
        have hP := (rep_permOfArr (isInv_of permP')).1
        rw [p_eq] at hs
        have hrc := rep_compA (rep_compA (CFSG.KS.Raw.rep_invCand hP) hA) hP
        have hmem := (mem_titsS_iff_sift hrc).1 hs
        have hgpt := (gpt_facts c0 c1 c2 c3 c4).2
        have ePI : invCand 1755 (unpack 1755 11 T614P) = unpack 1755 11 (pinv T614P) :=
          invCand_unpack permP'
        have hall : allN 2 (labEq t0 t1 t2 t3 t4) = true := allN_of_forall fun q hq2 => by
          have hq : q < 1755 := by omega
          have e1 := hrc ⟨q, hq⟩
          have hPq : (unpack 1755 11 T614P)[q]! < 1755 := hP.lt hq
          rw [compA_get hq, compA_get hPq, (hgpt _ hPq).1, ePI,
            unpack_get (hgpt _ hPq).2, unpack_get hq] at e1
          unfold labEq
          rw [Nat.eq_of_beq_eq_true piK, e1, lab_inv hmem ⟨q, hq⟩]
          exact Nat.beq_refl _
        rw [hl] at hall
        exact absurd hall (by decide)
    rw [hS]
    rfl
  · rw [hl] at h
    rw [inJ_eq cx]
    have h' : sfJ (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) = true := h
    rw [h', Bool.or_true]

theorem cG1 : C T614G1 := by quickRfl
theorem permG1 : permOK 1755 11 (mask 11) (1755 * 11) T614G1 (pinvS 1755 11 (mask 11) T614G1) =
    true := by quickRfl
theorem g1K : Nat.beq T614G1 (TitsText.F 1) = true := by quickRfl

theorem gen1_eq : titsGenArrs[1]! = unpack 1755 11 T614G1 := by
  rw [Nat.eq_of_beq_eq_true g1K]
  exact gen_eq (by norm_num)
theorem canKK : allN 7 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsK.S j)) = true := by
  quickRfl
theorem canNK : allN 10 (fun j => bAnd(canonK 1755 11 (mask 11) (1755 * 11) (TitsN.S j),
    canonK 1755 11 (mask 11) (1755 * 11) (TitsN.SI j))) = true := by quickRfl

theorem rep_unpack {x y : Nat} (h : permOK 1755 11 (mask 11) (1755 * 11) x y = true) :
    Rep 1755 (unpack 1755 11 x) (permOfArr 1755 (unpack 1755 11 x)) := by
  obtain ⟨h1, h2⟩ := invEqK_sound h
  rw [← h1] at h2
  exact (rep_permOfArr h2).1

theorem pt_of_rep {p : Nat} {g : Equiv.Perm (Fin 1755)} (h : Rep 1755 (unpack 1755 11 p) g)
    (z : Fin 1755) : (g z : Nat) = pg 11 (mask 11) p z := by
  rw [← h z, unpack_get z.2]

theorem tcomm_of_eqA {u v w : Array Nat} {σ τ ε : Equiv.Perm (Fin 1755)} (hu : Rep 1755 u σ)
    (hv : Rep 1755 v τ) (hw : Rep 1755 w ε) (h : eqA 1755 (commArr 1755 u v) w = true) :
    tcomm σ τ = ε :=
  eq_of_eqA (rep_commArr hu hv (CFSG.KS.Raw.isInvA_of_rep hu (CFSG.KS.Raw.rep_invCand hu))
    (CFSG.KS.Raw.isInvA_of_rep hv (CFSG.KS.Raw.rep_invCand hv))) hw h

theorem tcomm_pt {σ τ ε : Equiv.Perm (Fin 1755)} (hg : tcomm σ τ = ε) (y : Fin 1755) :
    σ (τ y) = τ (σ (ε y)) := by
  rw [← hg]
  unfold tcomm
  simp [Equiv.Perm.mul_apply]

theorem cmEq_of_pts {t0 t1 t2 t3 t4 H E : Nat} {σ τ ε : Equiv.Perm (Fin 1755)}
    (key : ∀ y, σ (τ y) = τ (σ (ε y)))
    (hσ : ∀ y : Fin 1755, (σ y : Nat) = uPt t0 t1 t2 t3 t4 y)
    (hτ : ∀ y : Fin 1755, (τ y : Nat) = pg 11 (mask 11) H y)
    (hε : ∀ y : Fin 1755, (ε y : Nat) = pg 11 (mask 11) E y) :
    cmEq t0 t1 t2 t3 t4 H E = true := by
  unfold cmEq
  refine allN_of_forall fun x hx8 => ?_
  have kx := congrArg Fin.val (key ⟨x, by omega⟩)
  simp only [hσ, hτ, hε] at kx
  beta_reduce
  rw [kx]
  exact Nat.beq_refl _

theorem upt_of_rep {t0 t1 t2 t3 t4 : Nat} (c0 : C t0) (c1 : C t1) (c2 : C t2) (c3 : C t3)
    (c4 : C t4) {σ : Equiv.Perm (Fin 1755)}
    (hU : Rep 1755 (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) σ)
    (y : Fin 1755) : (σ y : Nat) = uPt t0 t1 t2 t3 t4 y := by
  have hgpt := (gpt_facts c0 c1 c2 c3 c4).2
  have hG := rep_unpack permG1
  have e := hU y
  unfold outerArr at e
  rw [gen1_eq, compA_get y.2, unpack_get y.2] at e
  have hgy : pg 11 (mask 11) T614G1 y < 1755 := by
    rw [← unpack_get y.2]
    exact hG.lt y.2
  rw [(hgpt _ hgy).1] at e
  exact e.symm

theorem outer_fail {t0 t1 t2 t3 t4 : Nat} (c0 : C t0) (c1 : C t1) (c2 : C t2) (c3 : C t3)
    (c4 : C t4) (hinv : isInvA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
      (invCand 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) = true)
    {i : Nat} (hi : i < 3) (hfi : T614EL.any (cmEq t0 t1 t2 t3 t4 (TitsH.S i)) = false) :
    inE (commArr 1755 (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)))
      titsHArrs[i]!) = false := by
  cases he : inE (commArr 1755
      (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) titsHArrs[i]!)
  · rfl
  · exfalso
    unfold inE anyEq at he
    rw [eArrs_eq, List.any_eq_true] at he
    obtain ⟨c, hcE, heq⟩ := he
    obtain ⟨E, hEL, rfl⟩ := List.mem_map.1 hcE
    have hA := (rep_permOfArr hinv).1
    have hG := rep_unpack permG1
    have hU : Rep 1755 (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)))
        (permOfArr 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) *
          permOfArr 1755 (unpack 1755 11 T614G1)) := by
      unfold outerArr
      rw [gen1_eq]
      exact rep_compA hA hG
    have hH := rep_unpack (allN_spec permH i (by omega))
    rw [bindsH.2.2.2.2.1 i (by omega)] at heq
    have hEr := rep_unpack ((bAnd_iff _ _).1 (List.all_eq_true.1 kEL E hEL)).2
    have hg := tcomm_of_eqA hU hH hEr heq
    rw [List.any_eq_false] at hfi
    exact hfi E hEL (cmEq_of_pts (tcomm_pt hg) (upt_of_rep c0 c1 c2 c3 c4 hU) (pt_of_rep hH)
      (pt_of_rep hEr))

theorem outer_surv {t0 t1 t2 t3 t4 : Nat} (c0 : C t0) (c1 : C t1) (c2 : C t2) (c3 : C t3)
    (c4 : C t4) (h1 : kTests (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1)
      (pinv (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1)) = true) :
    (allLt 2 fun j => inK (conjArr
      (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) titsKArrs[j]!)) =
      true ∧
    (allLt 4 fun j => inK (commArr 1755
      (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) titsNArrs[j]!)) =
      true := by
  have cx : C (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) := cc (cc (cc (cc c0 c1) c2) c3) c4
  have hu : outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)) =
      unpack 1755 11 (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1) := by
    unfold outerArr
    rw [gen1_eq, cu cx cG1]
  unfold kTests at h1
  obtain ⟨kp, h1⟩ := (bAnd_iff _ _).1 h1
  obtain ⟨kc, h1⟩ := (bAnd_iff _ _).1 h1
  obtain ⟨kK, kN⟩ := (bAnd_iff _ _).1 h1
  have cU : C (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1) := cc cx cG1
  have eUI : invCand 1755 (unpack 1755 11 (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4)
      T614G1)) =
      unpack 1755 11 (pinv (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1)) :=
    invCand_unpack kp
  refine ⟨allLt_iff.2 fun j hj => ?_, allLt_iff.2 fun j hj => ?_⟩
  · have cK : C (TitsK.S j) := allN_spec canKK j (by omega)
    unfold conjArr
    rw [hu, bindsK.2.2.2.2.1 j (by omega), eUI, cu cU cK, cu (cc cU cK) kc,
      inK_eq (cc (cc cU cK) kc)]
    exact allN_spec kK j hj
  · have cN : C (TitsN.S j) := ((bAnd_iff _ _).1 (allN_spec canNK j (by omega))).1
    have cNI : C (TitsN.SI j) := ((bAnd_iff _ _).1 (allN_spec canNK j (by omega))).2
    have eNI := (invEqK_sound (allN_spec permN j (by omega))).1
    unfold commArr
    rw [hu, bindsN.2.2.2.2.1 j (by omega), eUI, eNI, cu kc cNI, cu (cc kc cNI) cU,
      cu (cc (cc kc cNI) cU) cN, inK_eq (cc (cc (cc kc cNI) cU) cN)]
    exact allN_spec kN j hj

theorem kKE : allL (fun E => memK (keyOf E) T614KE) T614EL = true := by quickRfl

theorem allL_mem {f : Nat → Bool} : ∀ {L : List Nat}, allL f L = true → ∀ {x}, x ∈ L →
    f x = true
  | [], _, _, hx => by simp at hx
  | a :: L, h, x, hx => by
    change bAnd(f a, allL f L) = true at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact h1
    · exact allL_mem h2 hx'

theorem bIf_true7195 {c t e : Bool} (ht : c = true → t = true) (he : c = false → e = true) :
    bIf(c, t, e) = true := by
  cases c
  · exact he rfl
  · exact ht rfl

theorem bIf_weak7195 {a b t : Bool} (hab : b = true → a = true) (h : bIf(a, t, true) = true) :
    bIf(b, t, true) = true := by
  cases b
  · rfl
  · rw [hab rfl] at h
    exact h

theorem rep_inj {p : Array Nat} {g : Equiv.Perm (Fin 1755)} (h : Rep 1755 p g) {y z : Nat}
    (hy : y < 1755) (hz : z < 1755) (e : p[y]! = p[z]!) : y = z := by
  have h1 := h ⟨y, hy⟩
  have h2 := h ⟨z, hz⟩
  have : g ⟨y, hy⟩ = g ⟨z, hz⟩ := Fin.ext (by rw [← h1, ← h2]; exact e)
  exact congrArg Fin.val (g.injective this)

theorem keyStep_true {t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI x : Nat} {fb : Bool} {k : Nat → Bool}
    (hfb : fb = true) (hk : ∀ z, z < 1755 →
      pg 11 (mask 11) H (gpt 11 (mask 11) t0 t1 t2 t3 t4 z) =
        uPt t0 t1 t2 t3 t4 (pg 11 (mask 11) H x) → k z = true) :
    keyStep t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI x fb k = true := by
  unfold keyStep
  simp only [strictB_eq7195]
  refine bIf_true7195 (fun hc => ?_) (fun _ => hfb)
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hc
  exact hk _ (Nat.blt_eq.mp h1) (Nat.eq_of_beq_eq_true h2)

theorem key_pt {t0 t1 t2 t3 t4 : Nat} (c0 : C t0) (c1 : C t1) (c2 : C t2) (c3 : C t3)
    (c4 : C t4) (hinv : isInvA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
      (invCand 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) = true)
    {H E : Nat} {τ : Equiv.Perm (Fin 1755)} (hH : Rep 1755 (unpack 1755 11 H) τ) (cE : C E)
    (hc : cmEq t0 t1 t2 t3 t4 H E = true) {x : Nat} (hx : x < 8) {z : Nat} (hz : z < 1755)
    (hzv : pg 11 (mask 11) H (gpt 11 (mask 11) t0 t1 t2 t3 t4 z) =
      uPt t0 t1 t2 t3 t4 (pg 11 (mask 11) H x)) :
    z = pg 11 (mask 11) T614G1 (pg 11 (mask 11) E x) := by
  have kx := Nat.eq_of_beq_eq_true (allN_spec hc x hx)
  rw [kx] at hzv
  unfold uPt at hzv
  obtain ⟨-, -, -, rE⟩ := canonK_facts cE
  obtain ⟨-, -, -, rG⟩ := canonK_facts cG1
  have hy : pg 11 (mask 11) T614G1 (pg 11 (mask 11) E x) < 1755 := rG _ (rE x (by omega))
  obtain ⟨-, hgpt⟩ := gpt_facts c0 c1 c2 c3 c4
  have h1 : (unpack 1755 11 H)[gpt 11 (mask 11) t0 t1 t2 t3 t4 z]! =
      (unpack 1755 11 H)[gpt 11 (mask 11) t0 t1 t2 t3 t4
        (pg 11 (mask 11) T614G1 (pg 11 (mask 11) E x))]! := by
    rw [unpack_get (hgpt _ hz).2, unpack_get (hgpt _ hy).2]
    exact hzv
  have e1 := rep_inj hH (hgpt _ hz).2 (hgpt _ hy).2 h1
  have h2 : (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))[z]! =
      (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))[
        pg 11 (mask 11) T614G1 (pg 11 (mask 11) E x)]! := by
    rw [(hgpt _ hz).1, (hgpt _ hy).1]
    exact e1
  exact rep_inj (rep_permOfArr hinv).1 hz hy h2

theorem keyTest_of {t0 t1 t2 t3 t4 : Nat} (c0 : C t0) (c1 : C t1) (c2 : C t2) (c3 : C t3)
    (c4 : C t4) (hinv : isInvA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
      (invCand 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) = true)
    {H HI E : Nat} {τ : Equiv.Perm (Fin 1755)} (hH : Rep 1755 (unpack 1755 11 H) τ)
    (hE : E ∈ T614EL) (hc : cmEq t0 t1 t2 t3 t4 H E = true) (i0 i1 i2 i3 i4 : Nat) {fb : Bool}
    (hfb : fb = true) : keyTest t0 t1 t2 t3 t4 i0 i1 i2 i3 i4 H HI fb = true := by
  have inj := fun {x : Nat} (hx : x < 8) {z : Nat} (hz : z < 1755) hzv =>
    key_pt c0 c1 c2 c3 c4 hinv hH (cEL hE) hc (x := x) hx hz hzv
  unfold keyTest
  refine keyStep_true hfb fun z hz hzv => ?_
  obtain rfl := inj (by omega) hz hzv
  refine keyStep_true hfb fun z hz hzv => ?_
  obtain rfl := inj (by omega) hz hzv
  refine keyStep_true hfb fun z hz hzv => ?_
  obtain rfl := inj (by omega) hz hzv
  refine keyStep_true hfb fun z hz hzv => ?_
  obtain rfl := inj (by omega) hz hzv
  refine keyStep_true hfb fun z hz hzv => ?_
  obtain rfl := inj (by omega) hz hzv
  refine keyStep_true hfb fun z hz hzv => ?_
  obtain rfl := inj (by omega) hz hzv
  refine keyStep_true hfb fun z hz hzv => ?_
  obtain rfl := inj (by omega) hz hzv
  refine keyStep_true hfb fun z hz hzv => ?_
  obtain rfl := inj (by omega) hz hzv
  have hm : memK (keyOf E) T614KE = true := allL_mem kKE hE
  unfold keyOf at hm
  exact hm

theorem POU_of_POUK {k t0 t1 t2 t3 t4 : Nat} (c0 : C t0) (c1 : C t1) (c2 : C t2) (c3 : C t3)
    (c4 : C t4) (hinv : isInvA 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))
      (invCand 1755 (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) = true)
    (h : POUK k t0 t1 t2 t3 t4 = true) : POU t0 t1 t2 t3 t4 = true := by
  unfold POUK at h
  unfold POU
  simp only [strictB_eq7195] at h ⊢
  refine bIf_weak7195 (fun hb => allN_of_forall fun i hi => ?_) h
  obtain ⟨E, hE, hc⟩ := List.any_eq_true.1 (allN_spec hb i hi)
  exact keyTest_of c0 c1 c2 c3 c4 hinv (rep_unpack (allN_spec permH i (by omega))) hE hc
    _ _ _ _ _ (List.any_eq_true.2 ⟨E, hE, hc⟩)

theorem outer_check_k : all5 1755 titsSLevels (fun a =>
    !(allLt 3 fun i => inE (commArr 1755 (outerArr a) titsHArrs[i]!)) ||
    ((allLt 2 fun j => inK (conjArr (outerArr a) titsKArrs[j]!)) &&
      (allLt 4 fun j => inK (commArr 1755 (outerArr a) titsNArrs[j]!)))) = true := by
  refine all5KQ_sound bindsS permS TitsS.hl
    (fun k t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 hinv h => ?_) T614OU.all
  replace h := POU_of_POUK c0 c1 c2 c3 c4 hinv h
  change bIf(allN 3 (fun i => T614EL.any (cmEq t0 t1 t2 t3 t4 (TitsH.S i))),
    strictB (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1) (fun U =>
      strictB (pinv U) (fun UI => kTests U UI)), true) = true at h
  cases hm : allN 3 (fun i => T614EL.any (cmEq t0 t1 t2 t3 t4 (TitsH.S i)))
  · obtain ⟨i, hi, hfi⟩ := exists_of_allN_false hm
    have hall : (allLt 3 fun i => inE (commArr 1755
        (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) titsHArrs[i]!)) =
        false := by
      cases ha : allLt 3 fun i => inE (commArr 1755
          (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) titsHArrs[i]!)
      · rfl
      · have := allLt_spec ha hi
        rw [outer_fail c0 c1 c2 c3 c4 hinv hi hfi] at this
        exact absurd this (by decide)
    show (!(allLt 3 fun i => inE (commArr 1755
      (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) titsHArrs[i]!)) ||
      _) = true
    rw [hall]
    rfl
  · rw [hm] at h
    have h1 : kTests (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1)
        (pinv (pc (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4) T614G1)) = true := by
      have h' := h
      simp only [strictB_eq7195] at h'
      exact h'
    obtain ⟨hK, hN⟩ := outer_surv c0 c1 c2 c3 c4 h1
    show (_ || ((allLt 2 fun j => inK (conjArr
      (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) titsKArrs[j]!)) &&
      (allLt 4 fun j => inK (commArr 1755
        (outerArr (unpack 1755 11 (prod5K 1755 11 (mask 11) t0 t1 t2 t3 t4))) titsNArrs[j]!)))) =
      true
    rw [hK, hN, Bool.and_self, Bool.or_true]

theorem batch7195 :
    (allLt 1755 (fun x => decide (x < 3) ||
        !(allLt 3 fun j => (titsRArrs[j]!)[x]! == x)) = true)
    ∧ (lettersOK 3 pWord = true ∧ eqA 1755 (pow5Arr pArr) (idA 1755) = true)
    ∧ ((∀ i < 5, lettersOK 4 (eXWord i) = true ∧ lettersOK 4 (eYWord i) = true) ∧
      eqA 1755 (eProdArr 0) (idA 1755) = true ∧ (allLt 5 fun i => inE (eGenArr i)) = true ∧
      (allLt 32 fun v => allLt 32 fun w => inE (compA 1755 (eProdArr v) (eProdArr w)) &&
        eqA 1755 (compA 1755 (eProdArr v) (eProdArr w))
          (compA 1755 (eProdArr w) (eProdArr v))) = true ∧
      (allLt 32 fun v => eqA 1755 (compA 1755 (eProdArr v) (eProdArr v)) (idA 1755)) = true ∧
      eArrs.Pairwise (fun a b => eqA 1755 a b = false) ∧
      eArrs.all (fun c => isInvA 1755 c (invCand 1755 c)) = true ∧
      (allLt 32 fun v => inJ (eProdArr v) && inK (eProdArr v)) = true ∧
      (allLt 5 fun i => inE (conjArr pArr (eGenArr i))) = true ∧ inE titsZArr = true)
    ∧ (all5 1755 titsSLevels (fun a => !(inJ a) ||
        !(eqA 1755 (compA 1755 a pArr) (compA 1755 pArr a)) || eqA 1755 a (idA 1755) ||
        eqA 1755 a titsZArr) = true)
    ∧ (all5 1755 titsHLevels (fun a =>
        !(allLt 3 fun i => inS (conjArr a titsSArrs[i]!)) || inS a) = true)
    ∧ (all5 1755 titsSLevels (fun a =>
        !(inS (compA 1755 (compA 1755 (invCand 1755 pArr) a) pArr)) || inJ a) = true)
    ∧ (all5 1755 titsSLevels (fun a =>
        !(allLt 3 fun i => inE (commArr 1755 (outerArr a) titsHArrs[i]!)) ||
        ((allLt 2 fun j => inK (conjArr (outerArr a) titsKArrs[j]!)) &&
          (allLt 4 fun j => inK (commArr 1755 (outerArr a) titsNArrs[j]!)))) = true) :=
  ⟨fix_check_k, p_check_k, e_check_k, cjp_check_k, nhs_check_k, ssp_check_k, outer_check_k⟩

end CertificateChecks.KernelSporSch.T614

end
