module

public import Certificates.Kernel.SuzFuse17320.Checks
public import Certificates.Kernel.SuzA17321.Facts
public import Certificates.Kernel.SuzThree13637.BindFacts
import CFSG.Certificates.Kernel.RankThree.F2Perm
import CFSG.Certificates.Kernel.Spor.BfsReplay
import CFSG.Certificates.NativeSchreierEnum
import CFSG.Sporadic.SuzOddCore.SmallChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzFuse17320

open CFSG.KS hiding levels
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump CertificateChecks.KernelSuzA17321
open CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.Certificates.Native CFSG.RankThree.PartOne CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 (allLt_iff)

theorem hXB : xBArr (levels ()) = unpack 1782 11 XB := by
  unfold xBArr
  exact rebuild_eq rbB

theorem pDK {i : Nat} (hi : i < 5) : permB 1782 11 (DK i) = true := Orb.allN_iff.1 pD i hi

theorem hDK {i : Nat} (hi : i < 5) : (dGens ())[i]! = unpack 1782 11 (DK i) :=
  (CFSG.KD.SuzThree13637.d_gen hi).1

theorem ppDK {i : Nat} (hi : i < 5) (e : Nat) : PP 1782 11 (pw3 (DK i) e) :=
  pp_ppow hw (pp_of_permB hw (pDK hi)) e

theorem powDK {i : Nat} (hi : i < 5) (e : Nat) :
    powArr 1782 (dGens ())[i]! e = unpack 1782 11 (pw3 (DK i) e) := by
  rw [hDK hi]
  exact pow_unpack hw (pDK hi) e

theorem ppEP (k : Nat) : PP 1782 11 (EP k) :=
  (ppDK (by norm_num) _).mul ((ppDK (by norm_num) _).mul ((ppDK (by norm_num) _).mul
    ((ppDK (by norm_num) _).mul (ppDK (by norm_num) _))))

theorem E_get {k : Nat} (hk : k < 243) : (dElts ())[k]! = unpack 1782 11 (EP k) := by
  rw [dElts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  unfold dProd
  rw [powDK (by norm_num : 0 < 5), powDK (by norm_num : 1 < 5), powDK (by norm_num : 2 < 5),
    powDK (by norm_num : 3 < 5), powDK (by norm_num : 4 < 5),
    compA_PP (ppDK (by norm_num) _) (ppDK (by norm_num) _),
    compA_PP (ppDK (by norm_num) _) ((ppDK (by norm_num) _).mul (ppDK (by norm_num) _)),
    compA_PP (ppDK (by norm_num) _)
      ((ppDK (by norm_num) _).mul ((ppDK (by norm_num) _).mul (ppDK (by norm_num) _))),
    compA_PP (ppDK (by norm_num) _) ((ppDK (by norm_num) _).mul
      ((ppDK (by norm_num) _).mul ((ppDK (by norm_num) _).mul (ppDK (by norm_num) _))))]
  rfl

theorem ord_of {G : Nat} (hp : permB 1782 11 G = true)
    (h3 : Nat.beq (pw3 G 3) (pidn 1782 11) = true) (h1 : Nat.beq G (pidn 1782 11) = false) :
    eqA 1782 (powArr 1782 (unpack 1782 11 G) 3) (idA 1782) = true ∧
      eqA 1782 (unpack 1782 11 G) (idA 1782) = false := by
  rw [pow_unpack hw hp, idA_eq hw, eqA_PP (pp_ppow hw (pp_of_permB hw hp) 3) (PP.id hw),
    eqA_PP (pp_of_permB hw hp) (PP.id hw)]
  exact ⟨h3, h1⟩

noncomputable def dGP (i : Nat) : Equiv.Perm (Fin 1782) :=
  CFSG.Monster.B.Co2.permOfArr 1782 (unpack 1782 11 (DK i))

theorem prDK {i : Nat} (hi : i < 5) : Orb.PRep 1782 11 (DK i) (dGP i) :=
  Orb.prep_of_rep (CFSG.RankThree.Native.rep_of_validA (validA_of (pDK hi)))

theorem prPw {i : Nat} (hi : i < 5) (e : Nat) : Orb.PRep 1782 11 (pw3 (DK i) e) (dGP i ^ e) := by
  induction e with
  | zero => exact Orb.prep_pidn (by norm_num) (by norm_num)
  | succ e ih =>
    have e1 : pw3 (DK i) (e + 1) = pcomp 1782 11 (mask 11) (DK i) (pw3 (DK i) e) :=
      PF.strictN_eqP (pw3 (DK i) e) (fun q => pcomp 1782 11 (mask 11) (DK i) q)
    rw [e1, pow_succ']
    exact Orb.prep_pcomp (by norm_num) (prDK hi) ih

theorem prEP (k : Nat) : Orb.PRep 1782 11 (EP k) (dGP 0 ^ digit3 k 0 * (dGP 1 ^ digit3 k 1 *
    (dGP 2 ^ digit3 k 2 * (dGP 3 ^ digit3 k 3 * dGP 4 ^ digit3 k 4)))) :=
  Orb.prep_pcomp (by norm_num) (prPw (by norm_num) _) (Orb.prep_pcomp (by norm_num)
    (prPw (by norm_num) _) (Orb.prep_pcomp (by norm_num) (prPw (by norm_num) _)
      (Orb.prep_pcomp (by norm_num) (prPw (by norm_num) _) (prPw (by norm_num) _))))

theorem prep_mulDK {i E : Nat} {g : Equiv.Perm (Fin 1782)} (hi : i < 5)
    (h : PP 1782 11 E ∧ Orb.PRep 1782 11 E g) :
    PP 1782 11 (mulDK i E) ∧ Orb.PRep 1782 11 (mulDK i E) (dGP i * g) :=
  ⟨(pp_of_permB hw (pDK hi)).mul h.1, Orb.prep_pcomp (by norm_num) (prDK hi) h.2⟩

theorem walkD2_spec {k E : Nat} {g : Equiv.Perm (Fin 1782)}
    (hE : PP 1782 11 E ∧ Orb.PRep 1782 11 E g) (h : walkD2 k E = true) {a : Nat} (ha : a < 3) :
    ∃ F, (PP 1782 11 F ∧ Orb.PRep 1782 11 F (dGP 0 ^ a * g)) ∧ fuseK (k + a) F = true := by
  unfold walkD2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  interval_cases a
  · rw [pow_zero, one_mul]
    exact ⟨E, hE, h0⟩
  · rw [pow_one]
    exact ⟨_, prep_mulDK (by norm_num) hE, h1⟩
  · rw [pow_two, mul_assoc]
    exact ⟨_, prep_mulDK (by norm_num) (prep_mulDK (by norm_num) hE), h2⟩

theorem walkD1_spec {k E : Nat} {g : Equiv.Perm (Fin 1782)}
    (hE : PP 1782 11 E ∧ Orb.PRep 1782 11 E g) (h : walkD1 k E = true) {a b : Nat} (ha : a < 3)
    (hb : b < 3) : ∃ F, (PP 1782 11 F ∧ Orb.PRep 1782 11 F (dGP 0 ^ a * (dGP 1 ^ b * g))) ∧
      fuseK (k + 3 * b + a) F = true := by
  unfold walkD1 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  interval_cases b
  · rw [pow_zero, one_mul]
    exact walkD2_spec hE h0 ha
  · rw [pow_one]
    exact walkD2_spec (prep_mulDK (by norm_num) hE) h1 ha
  · rw [pow_two, mul_assoc]
    exact walkD2_spec (prep_mulDK (by norm_num) (prep_mulDK (by norm_num) hE)) h2 ha

theorem walkD0_spec {k E : Nat} {g : Equiv.Perm (Fin 1782)}
    (hE : PP 1782 11 E ∧ Orb.PRep 1782 11 E g) (h : walkD0 k E = true) {a b c : Nat} (ha : a < 3)
    (hb : b < 3) (hc : c < 3) :
    ∃ F, (PP 1782 11 F ∧ Orb.PRep 1782 11 F (dGP 0 ^ a * (dGP 1 ^ b * (dGP 2 ^ c * g)))) ∧
      fuseK (k + 9 * c + 3 * b + a) F = true := by
  unfold walkD0 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  interval_cases c
  · rw [pow_zero, one_mul]
    exact walkD1_spec hE h0 ha hb
  · rw [pow_one]
    exact walkD1_spec (prep_mulDK (by norm_num) hE) h1 ha hb
  · rw [pow_two, mul_assoc]
    exact walkD1_spec (prep_mulDK (by norm_num) (prep_mulDK (by norm_num) hE)) h2 ha hb

theorem fuseK_all {k : Nat} (hk : k < 243) : fuseK k (EP k) = true := by
  have hs : ∀ j < 9, fuseS j = true := by
    intro j hj
    interval_cases j
    exacts [s0, s1, s2, s3, s4, s5, s6, s7, s8]
  obtain ⟨j, c, b, a, hj, hc, hb, ha, rfl⟩ : ∃ j c b a, j < 9 ∧ c < 3 ∧ b < 3 ∧ a < 3 ∧
      k = 27 * j + 9 * c + 3 * b + a :=
    ⟨k / 27, k / 9 % 3, k / 3 % 3, k % 3, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨F, ⟨hpF, hF⟩, hf⟩ := walkD0_spec ⟨ppEP _, prEP _⟩ (hs j hj) ha hb hc
  have hEq : F = EP (27 * j + 9 * c + 3 * b + a) := by
    refine Nat.eq_of_beq_eq_true ?_
    rw [← eqA_PP hpF (ppEP _), CFSG.Monster.B.Co2.eqA_iff (Orb.rep_unpack hF)
      (Orb.rep_unpack (prEP _))]
    have d0 : digit3 (27 * j + 9 * c + 3 * b + a) 0 = a := by
      simp only [digit3, Nat.reducePow, Nat.div_one]
      omega
    have d1 : digit3 (27 * j + 9 * c + 3 * b + a) 1 = b := by
      simp only [digit3, Nat.reducePow]
      omega
    have d2 : digit3 (27 * j + 9 * c + 3 * b + a) 2 = c := by
      simp only [digit3, Nat.reducePow]
      omega
    have d3 : digit3 (27 * j + 9 * c + 3 * b + a) 3 = digit3 (27 * j) 3 := by
      simp only [digit3, Nat.reducePow]
      omega
    have d4 : digit3 (27 * j + 9 * c + 3 * b + a) 4 = digit3 (27 * j) 4 := by
      simp only [digit3, Nat.reducePow]
      omega
    have e0 : digit3 (27 * j) 0 = 0 := by
      simp only [digit3, Nat.reducePow, Nat.div_one]
      omega
    have e1 : digit3 (27 * j) 1 = 0 := by
      simp only [digit3, Nat.reducePow]
      omega
    have e2 : digit3 (27 * j) 2 = 0 := by
      simp only [digit3, Nat.reducePow]
      omega
    rw [d0, d1, d2, d3, d4, e0, e1, e2, pow_zero, pow_zero, pow_zero, one_mul, one_mul, one_mul]
  rw [← hEq]
  exact hf

theorem tgt_eq (k : Nat) : (if (fuseCls[k]! == 0) = true then xAArr (levels ()) else
    xBArr (levels ())) = unpack 1782 11 (tgt k) ∧ PP 1782 11 (tgt k) := by
  unfold tgt
  cases (fuseCls[k]! == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
    exact ⟨hXB, pp_of_permB hw pXB⟩
  · simp only [↓reduceIte, Bool.cond_true]
    exact ⟨KernelSuzA17321.hX, pp_of_permB hw KernelSuzA17321.pX⟩

theorem reb_prep {beta : Array Nat} (h : (reb beta).2.2 = true) :
    ∃ γ : Equiv.Perm (Fin 1782), Orb.PRep 1782 11 (reb beta).1 γ := by
  have hok := reb_ok _ h
  have key := CFSG.KS.BfsReplay.forIn_range'_yield 6 0 (idA 1782, idA 1782)
    (fun i (s : Array Nat × Array Nat) =>
      (pure (ForInStep.yield (compA 1782 s.1 (levels ())[i]!.tr[(levels ())[i]!.pos[s.2[beta[i]!]!]!]!,
        compA 1782 (levels ())[i]!.trInv[(levels ())[i]!.pos[s.2[beta[i]!]!]!]! s.2)) :
          Id (ForInStep (Array Nat × Array Nat))))
    (fun j s => Orb.RebSt 1782 11 s.1 s.2
      (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => beta[l]!) j).1
      (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => beta[l]!) j).2.1)
    (fun j hj s hs => by
      refine ⟨_, rfl, ?_⟩
      rw [Nat.zero_add, reb_succ]
      obtain ⟨hb, hk⟩ := hok j hj
      obtain ⟨A, hT⟩ := Orb.agree_levelK Suz2306.binds Suz2306.perm hbl hj (SuzC.hl j hj)
      exact (Orb.rebStep_spec (by norm_num) A hT hs hb hk).2)
    (Orb.rebSt_init (by norm_num) (by norm_num))
  obtain ⟨-, -, γ, -, -, hA, -⟩ := key
  exact ⟨γ, hA⟩

theorem inP_rebuild {beta : Array Nat} (h : (reb beta).2.2 = true) :
    inP (levels ()) (rebuild (levels ()) beta) = true := by
  have hok := reb_ok _ h
  have hA := smallChain_arrays
  have hF := CFSG.Certificates.chainCheckFacts smallChain_check.1
  have hb6 : smallChain.baseCount = 6 := hA.base_size.symm
  have key := CFSG.KS.BfsReplay.forIn_range'_yield 6 0 (idA 1782, idA 1782)
    (fun i (s : Array Nat × Array Nat) =>
      (pure (ForInStep.yield (compA 1782 s.1 (levels ())[i]!.tr[(levels ())[i]!.pos[s.2[beta[i]!]!]!]!,
        compA 1782 (levels ())[i]!.trInv[(levels ())[i]!.pos[s.2[beta[i]!]!]!]! s.2)) :
          Id (ForInStep (Array Nat × Array Nat))))
    (fun j s => Orb.RebSt 1782 11 s.1 s.2
      (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => beta[l]!) j).1
      (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => beta[l]!) j).2.1 ∧
      ∃ γ ∈ suzM, CFSG.Monster.B.Co2.Rep 1782 s.1 γ)
    (fun j hj s hs => by
      refine ⟨_, rfl, ?_⟩
      rw [Nat.zero_add, reb_succ]
      obtain ⟨hb, hk⟩ := hok j hj
      obtain ⟨A, hT⟩ := Orb.agree_levelK Suz2306.binds Suz2306.perm hbl hj (SuzC.hl j hj)
      obtain ⟨hpos, hst⟩ := Orb.rebStep_spec (by norm_num) A hT hs.1 hb hk
      obtain ⟨γ, hγ, ha⟩ := hs.2
      have hkL : (CFSG.Certificates.ChainArrays.lev 1782 smallStrongArrs smallBaseNat.toArray j).pos[
          s.2[beta[j]!]!]! <
          (CFSG.Certificates.ChainArrays.lev 1782 smallStrongArrs smallBaseNat.toArray j).pts.size := by
        rw [hpos, ← A.cnt]
        exact hk
      have hj' : j < smallChain.baseCount := by omega
      refine ⟨hst, _, mul_mem hγ ?_,
        CFSG.Monster.B.Co2.rep_compA ha (hA.rep_levT hF hj' hkL)⟩
      rw [← smallChain_originalSubgroup, ← smallChain.levelSubgroup_zero_eq_original smallChain_valid]
      exact smallChain.levelSubgroup_antitone 0 j (Nat.zero_le _) (hA.levT_mem hF hj' hkL))
    ⟨Orb.rebSt_init (by norm_num) (by norm_num), 1, one_mem _, CFSG.Monster.B.Co2.rep_idA⟩
  obtain ⟨-, γ, hγ, ha⟩ := key
  have hr : CFSG.Monster.B.Co2.Rep 1782 (rebuild (levels ()) beta) γ := by
    unfold rebuild
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one]
    exact ha
  exact (mem_suzM_iff_siftA hr).2 hγ

theorem fuse_k {k : Nat} (hk : k < 243) (h0 : k ≠ 0) :
    (validA 1782 (fuseArr (levels ()) k) && inP (levels ()) (fuseArr (levels ()) k) &&
      eqA 1782 (conjA 1782 (fuseArr (levels ()) k) (dElts ())[k]!)
        (if (fuseCls[k]! == 0) = true then xAArr (levels ()) else xBArr (levels ()))) = true := by
  have hf := fuseK_all hk
  unfold fuseK fuseKT at hf
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hf
  obtain ⟨hr, hc⟩ := hf.resolve_left fun h => h0 (Nat.eq_of_beq_eq_true h)
  obtain ⟨γ, hγ⟩ := reb_prep hr
  replace hγ : Orb.PRep 1782 11 (HK k) γ := hγ
  have hi : inP (levels ()) (fuseArr (levels ()) k) = true := inP_rebuild hr
  rw [hi]
  have hH : fuseArr (levels ()) k = unpack 1782 11 (HK k) := by
    unfold fuseArr
    exact rebuild_eq hr
  obtain ⟨ht, hpt⟩ := tgt_eq k
  have rH := Orb.rep_unpack hγ
  have rE := CFSG.RankThree.Native.rep_of_validA (validA_of (permB_of_pp (ppEP k)))
  have rT := CFSG.RankThree.Native.rep_of_validA (validA_of (permB_of_pp hpt))
  have hv : validA 1782 (unpack 1782 11 (HK k)) = true :=
    CFSG.RankThree.Native.F2.validA_of_rep rH
  have hmul : γ * CFSG.Monster.B.Co2.permOfArr 1782 (unpack 1782 11 (EP k)) =
      CFSG.Monster.B.Co2.permOfArr 1782 (unpack 1782 11 (tgt k)) * γ := by
    have p1 := Orb.prep_pcomp (by norm_num) hγ (Orb.prep_of_rep rE)
    have p2 := Orb.prep_pcomp (by norm_num) (Orb.prep_of_rep rT) hγ
    rw [Nat.eq_of_beq_eq_true hc] at p1
    exact CFSG.Monster.B.Co2.Rep.unique (Orb.rep_unpack p1) (Orb.rep_unpack p2)
  have hg : CFSG.Monster.B.Co2.permOfArr 1782 (unpack 1782 11 (HK k)) = γ :=
    CFSG.RankThree.Native.permOfArr_eq_of_rep rH
  have hc' : eqA 1782 (conjA 1782 (unpack 1782 11 (HK k)) (unpack 1782 11 (EP k)))
      (unpack 1782 11 (tgt k)) = true := by
    rw [CFSG.Monster.B.Co2.eqA_iff (CFSG.RankThree.Native.rep_conjA hv rE) rT, hg, hmul,
      mul_inv_cancel_right]
  simp only [hH, E_get hk, ht, hv, hc', Bool.and_self]

theorem fuse_ok : fuseCheck () = true := by
  obtain ⟨a3, a1⟩ := ord_of KernelSuzA17321.pX ordX.1 ordX.2.1
  obtain ⟨b3, b1⟩ := ord_of pXB ordX.2.2.1 ordX.2.2.2
  have vA : validA 1782 (unpack 1782 11 XP) = true := validA_of KernelSuzA17321.pX
  have vB : validA 1782 (unpack 1782 11 XB) = true := validA_of pXB
  have iA : inP (levels ()) (unpack 1782 11 XP) = true := by
    rw [← KernelSuzA17321.hX]
    exact inP_rebuild KernelSuzA17321.rbAll.1
  have iB : inP (levels ()) (unpack 1782 11 XB) = true := by
    rw [← hXB]
    exact inP_rebuild rbB
  have z1 : (fuseTuples.size == 243) = true := by decide +kernel
  have z2 : (fuseCls.size == 243) = true := by decide +kernel
  have hall : allLt 243 (fun k => k == 0 || (validA 1782 (fuseArr (levels ()) k) &&
      inP (levels ()) (fuseArr (levels ()) k) &&
      eqA 1782 (conjA 1782 (fuseArr (levels ()) k) (dElts ())[k]!)
        (if (fuseCls[k]! == 0) = true then xAArr (levels ()) else xBArr (levels ())))) = true := by
    rw [allLt_iff]
    intro k hk
    by_cases h0 : k = 0
    · subst h0
      rfl
    · rw [fuse_k hk h0, Bool.or_true]
  unfold fuseCheck
  simp only []
  rw [hall]
  rw [KernelSuzA17321.hX, hXB]
  simp only [vA, vB, iA, iB, a3, a1, b3, b1, z1, z2, Bool.not_false, Bool.and_self]

end CertificateChecks.KernelSuzFuse17320

end
