module

public import Certificates.Kernel.Fi22Twist.CjChk
public import Certificates.Kernel.Fi22Twist.DfChk
public import Certificates.Kernel.Fi22Twist.TxFacts
public import Certificates.Kernel.Fi22Twist.PrFacts
public import CFSG.Certificates.Kernel.Fi22Twist.ConjSound
public import CFSG.Certificates.Kernel.Fi22Twist.LeafSound
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CertificateChecks.KernelFi22Rank.Q2 CFSG.KS.Raw
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative

set_option maxRecDepth 400000

#kc_forall_tree cj431009rcAll (fun c => ch431009rc c = true) 81 CFSG.KD.Fi22Twist.ch431009rc

#kc_forall_tree cj431009cpAll (fun r => ch431009cp r = true) 21 CFSG.KD.Fi22Twist.ch431009cp

#kc_forall_tree cj431009dfAll (fun k => ch431009df_ k = true) 15
  CertificateChecks.KernelFi22Twist.ch431009df_

@[expose] noncomputable def dSub (j : ℕ) : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure {permOfArr 3510 (repX j), permOfArr 3510 (repY j), permOfArr 3510 (repZ j)}

theorem df_all {j k : ℕ} (hj : j < 5) (hk : k < 27) : dfK DF TX.F j k = true := by
  have hq : (27 * j + k) / 9 < 15 := by omega
  have h := CFSG.KS.allBlk_spec (cj431009dfAll _ hq) ((27 * j + k) % 9) (Nat.mod_lt _ (by norm_num))
  have h1 : dfK DF TX.F ((9 * ((27 * j + k) / 9) + (27 * j + k) % 9) / 27)
      ((9 * ((27 * j + k) / 9) + (27 * j + k) % 9) % 27) = true := h
  have e : 9 * ((27 * j + k) / 9) + (27 * j + k) % 9 = 27 * j + k := by omega
  have e2 : (27 * j + k) / 27 = j := by omega
  have e3 : (27 * j + k) % 27 = k := by omega
  rwa [e, e2, e3] at h1

theorem rep_prep {k : ℕ} (hk : k < 15) :
    PRep 3510 12 (MonoidHom.id _) (rowR TX.F k) (permOfArr 3510 (repXYZ[k]!)) := by
  rw [(repXYZ_facts.2 k hk).1]
  exact prep_of_PP (repXYZ_facts.2 k hk).2

theorem df_mem {j : ℕ} (hj : j < 5) : ∀ k < 27, ∃ y ∈ dSub j,
    ∀ z < 3510, ap (DF (27 * j + k)) z = pt (MonoidHom.id _) y z := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  obtain ⟨h0, h1, h2, h3⟩ := dfK_sound (df_all hj hk)
  have step : ∀ (m d : ℕ), m < 3 → d ≤ k → 0 < d → d ≤ 9 →
      (∀ z < 3510, ap (DF (27 * j + k)) z =
        ap (DF (27 * j + k - d)) (ap (rowR TX.F (3 * j + m)) z)) →
      permOfArr 3510 (repXYZ[3 * j + m]!) ∈ dSub j →
      ∃ y ∈ dSub j, ∀ z < 3510, ap (DF (27 * j + k)) z = pt (MonoidHom.id _) y z := by
    intro m d hm hdk hd0 hd9 hrel hmem
    obtain ⟨y, hy, hyz⟩ := ih (k - d) (by omega) (by omega)
    have hr := rep_prep (k := 3 * j + m) (by omega)
    refine ⟨y * permOfArr 3510 (repXYZ[3 * j + m]!), mul_mem hy hmem, fun z hz => ?_⟩
    have e : 27 * j + k - d = 27 * j + (k - d) := by omega
    rw [hrel z hz, e, ap_eq hr hz, hyz _ (pt_lt _ _ hz), pt_mul]
  have hx : permOfArr 3510 (repXYZ[3 * j + 0]!) ∈ dSub j :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : permOfArr 3510 (repXYZ[3 * j + 1]!) ∈ dSub j :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hz : permOfArr 3510 (repXYZ[3 * j + 2]!) ∈ dSub j :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  by_cases hk0 : k = 0
  · refine ⟨1, one_mem _, fun z hz => ?_⟩
    rw [pt_one]
    exact h0 hk0 z hz
  by_cases hk3 : k % 3 ≠ 0
  · exact step 2 1 (by norm_num) (by omega) (by norm_num) (by norm_num) (h1 hk3) hz
  by_cases hk9 : k % 9 ≠ 0
  · exact step 1 3 (by norm_num) (by omega) (by norm_num) (by norm_num)
      (h2 (by omega) (by omega) hk9) hy
  · exact step 0 9 (by norm_num) (by omega) (by norm_num) (by norm_num)
      (h3 (by omega) (by omega)) hx

theorem q2_e27_conj (A : Subgroup (Equiv.Perm (Fin 3510)))
    (hA : A ≤ Subgroup.closure (permsA 3510 (qGens 2))) (hcard : Nat.card A = 27)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1) :
    ∃ j < 5, ∃ h ∈ Subgroup.closure ({x | ∃ r < 21, permOfArr 3510 (unpack 3510 12 (CJ r)) = x} ∪
        (Subgroup.closure (permsA 3510 (qGens 2)) : Set (Equiv.Perm (Fin 3510)))),
      ∀ x ∈ A, h * x * h⁻¹ ∈ dSub j := by
  obtain ⟨T, e, P, hT⟩ := q2_tab
  obtain ⟨c, hc, hle⟩ := P.e27_le_record A (by rw [hT]; exact hA) hcard hcomm hexp
  have hcp : ∀ r < 21, PRep 3510 12 (MonoidHom.id _) (CJ r)
      (permOfArr 3510 (unpack 3510 12 (CJ r))) :=
    fun r hr => prep_of_PP (PP_of_permOK szA (cj431009cpAll r hr))
  obtain ⟨j, hj, h, hh, hconj⟩ := P.conj_records (DF := DF) (CG := CJ) (RC := RC) (nG := 21)
    (D := dSub) Function.injective_id hcp (fun j hj k hk => df_mem hj k hk)
    (fun c hc => cj431009rcAll c hc) hc
  refine ⟨j, hj, h, Subgroup.closure_mono ?_ hh, fun x hx => hconj x (hle hx)⟩
  rintro _ (⟨r, hr, rfl⟩ | ⟨i, hi, rfl⟩)
  · exact Or.inl ⟨r, hr, rfl⟩
  · refine Or.inr ?_
    rw [← hT]
    exact P.e_mem hi

end CertificateChecks.KernelFi22Twist

end
