module

public import Certificates.Kernel.Sporadic.ON6.Checks
public import Certificates.Kernel.Sporadic.ON6.ChecksM
public import Certificates.Kernel.Sporadic.ON6.ChecksL
public import Certificates.Kernel.Sporadic.ON6.ChecksQ
public import CFSG.Certificates.Kernel.Spor.ChainGKSound
public import Certificates.Kernel.Sporadic.ON5.Final
public import CFSG.Sporadic.Schreier.ONCheckSmallInputs
public import CFSG.Sporadic.Schreier.ONCheckSmallInputs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.LocalCompSPCode
import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON6K.tAll CertificateChecks.KernelSpor.ON6K.tSch 12
#kon_join CertificateChecks.KernelSpor.ON6K.mAll CertificateChecks.KernelSpor.ON6K.mSch 90
#kon_join CertificateChecks.KernelSpor.ON6K.lAll CertificateChecks.KernelSpor.ON6K.lSch 90
#kon_join CertificateChecks.KernelSpor.ON6K.pAll CertificateChecks.KernelSpor.ON6K.pSch 28
#kon_join CertificateChecks.KernelSpor.ON6K.qAll CertificateChecks.KernelSpor.ON6K.qSch 90

namespace CertificateChecks.KernelSpor.ON6K

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.KS.CH CFSG.ONSchreier CFSG.ONSchreier.Native
open CertificateChecks.KernelSpor.ON3 (allBelowN_iff)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  CFSG.KLC.E8.allN_iff

theorem sch_of {n nb g c ns : Nat} {F FI : Nat → Nat → Nat} {B LEN Mr : Nat → Nat}
    {IDX : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat → Nat}
    (hall : ∀ s < ns, schSl n nb g c F FI B LEN Mr IDX PTS POS PAR LAB s = true)
    (hg : 0 < g) (hns : nb * c ≤ ns) (hM : ∀ i < nb, Mr i ≤ g * c) :
    ∀ i < nb, ∀ h < Mr i, schAll n nb F FI B LEN Mr IDX PTS POS PAR LAB i h = true := by
  intro i hi h hh
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have := hM i hi
      rw [h0] at this
      omega
    · exact h0
  have ht : h / g < c := by
    have := hM i hi
    rw [Nat.div_lt_iff_lt_mul hg]
    rw [Nat.mul_comm] at this
    omega
  have hs : c * i + h / g < ns := by
    have : c * i + c ≤ nb * c := by
      rw [Nat.mul_comm nb c]
      have := Nat.mul_le_mul_left c (show i + 1 ≤ nb by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      exact this
    omega
  have h0 := hall (c * i + h / g) hs
  unfold schSl at h0
  rw [strictB_eq, strictB_eq] at h0
  have e1 : Nat.div (c * i + h / g) c = i := by
    change (c * i + h / g) / c = i
    rw [Nat.mul_add_div hc, Nat.div_eq_of_lt ht, Nat.add_zero]
  have e2 : Nat.mul (Nat.mod (c * i + h / g) c) g = h / g * g := by
    change (c * i + h / g) % c * g = h / g * g
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
  rw [e1, e2] at h0
  have h1 := allN_spec h0 (h % g) (Nat.mod_lt _ hg)
  rw [strictB_eq] at h1
  have e3 : Nat.add (h / g * g) (h % g) = h := by
    change h / g * g + h % g = h
    rw [Nat.mul_comm]
    exact Nat.div_add_mod h g
  rw [e3, Eq.mpr Nat.blt_eq hh] at h1
  exact h1

theorem getD_app {m : Nat} {D : Array (List Int)} {j : Nat} (hj : m ≤ j) (hj2 : j < m + D.size) :
    (Array.replicate m ([] : List Int) ++ D)[j]! = D[j - m]! := by
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos _ (j - m) (by omega),
    Array.getElem_append_right (by simp; omega)]
  simp

theorem chain_of {n s nb m : Nat} {F FI : Nat → Nat → Nat} {B LEN Mr : Nat → Nat}
    {IDX : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat → Nat} {S : Array (Array Nat)}
    {D : Array (List Int)} {base : Array Nat}
    (hS : S.size = s) (hDm : m + D.size = s) (hb : base.size = nb) (hB : ∀ k < nb, base[k]! = B k)
    (hD : ∀ j, m ≤ j → j < s → ∀ l ∈ D[j - m]!, l ≠ 0 ∧ l.natAbs ≤ j)
    (hsm : smallK n s nb m F FI B LEN Mr IDX PTS POS PAR LAB S D = true)
    (hsch : ∀ i < nb, ∀ h < Mr i, schAll n nb F FI B LEN Mr IDX PTS POS PAR LAB i h = true) :
    fullChainOK n m S base (Array.replicate m [] ++ D) 2 = true ∧
      cOrbitSizes n S base = (List.range nb).map Mr := by
  unfold smallK at hsm
  simp only [Bool.and_eq_true] at hsm
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hsm
  refine fullChainG_sound (s := s) (F := F) (FI := FI) (B := B) (LEN := LEN) (IDX := IDX) hS
    (by simp; omega) (by omega) (fun j hj x hx => ?_) (fun j hmj hj => ?_) hb
    (fun k hk => ⟨hB k hk, ?_⟩) (fun i hi => ?_) (fun i hi => ?_) (fun i hi k hk => ?_)
    (fun i hi z hz => ?_) (fun i hi h hh j hj => allN_spec (hsch i hi h hh) j hj) h4
  · have := allN_spec (allN_spec h1 j hj) x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1.1.symm, this.1.1.2, this.1.2, this.2⟩
  · rw [getD_app hmj (by omega)]
    refine ⟨hD j hmj hj, fun x hx => ?_⟩
    have := allN_spec h2 j hj
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with h | h
    · omega
    · exact Nat.eq_of_beq_eq_true (allN_spec h x hx)
  all_goals have hh := allN_spec h3
  all_goals simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  · exact (hh k hk).1.1.1.1
  · exact (hh i hi).1.1.1.2
  · exact (hh i hi).1.1.2
  · exact allN_spec (hh i hi).1.2 k hk
  · exact allN_spec (hh i hi).2 z hz

theorem gens_of {n s k : Nat} {F FI : Nat → Nat → Nat} {G S : Array (Array Nat)}
    (hk : k ≤ s) (hS : S.size = s) (hGs : G.size = k)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hsz : ∀ j < k, (G[j]!).size = n) (heq : ∀ j < k, peq n G[j]! S[j]! = true) :
    allBelowN k (fun j => peq n G[j]! S[j]! && pisInv n G[j]! (pinvCand n G[j]!)) = true := by
  rw [allBelowN_iff]
  intro j hj
  rw [heq j hj, Bool.true_and]
  have hp := heq j hj
  unfold peq at hp
  rw [allBelowN_iff] at hp
  refine CertificateChecks.KernelSpor.ON5K.pisInv_of (f := F j) (fi := FI j) (hsz j hj)
    (fun x hx => ?_) fun x hx => ⟨(hF j (by omega) x hx).2.1, (hF j (by omega) x hx).2.2.2⟩
  have := hp x hx
  rw [beq_iff_eq] at this
  rw [this]
  exact (hF j (by omega) x hx).1

theorem small_ok {n s nb : Nat} {F FI : Nat → Nat → Nat} {B LEN Mr : Nat → Nat}
    {IDX : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat → Nat} (ch : Data.SmallChain)
    (hdeg : ch.degree = n) (hS : ch.strongGenerators.size = s) (hk : ch.generators.size ≤ s)
    (hDm : ch.generators.size + ch.derivations.size = s) (hb : ch.base.size = nb)
    (hB : ∀ k < nb, ch.base[k]! = B k)
    (hD : ∀ j, ch.generators.size ≤ j → j < s → ∀ l ∈ ch.derivations[j - ch.generators.size]!,
      l ≠ 0 ∧ l.natAbs ≤ j)
    (hsm : smallK n s nb ch.generators.size F FI B LEN Mr IDX PTS POS PAR LAB ch.strongGenerators
      ch.derivations = true)
    (hsch : ∀ i < nb, ∀ h < Mr i, schAll n nb F FI B LEN Mr IDX PTS POS PAR LAB i h = true)
    (hsz : ∀ j < ch.generators.size, (ch.generators[j]!).size = n)
    (heq : ∀ j < ch.generators.size, peq n ch.generators[j]! ch.strongGenerators[j]! = true) :
    smallChainOK n ch = true ∧ cOrbitSizes n ch.strongGenerators ch.base = (List.range nb).map Mr := by
  have hc := chain_of hS hDm hb hB hD hsm hsch
  refine ⟨?_, hc.2⟩
  have hsm' := hsm
  unfold smallK at hsm'
  simp only [Bool.and_eq_true] at hsm'
  have hF : ∀ j < s, ∀ x < n, (ch.strongGenerators[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧
      FI j (F j x) = x := by
    intro j hj x hx
    have := allN_spec (allN_spec hsm'.1.1.1 j hj) x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1.1.symm, this.1.1.2, this.1.2, this.2⟩
  unfold smallChainOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨hdeg, hS ▸ hk⟩, gens_of hk hS rfl hF hsz heq⟩, hc.1⟩

theorem t_ok : smallChainOK 32 Data.T32Chain = true ∧
    cOrbitSizes 32 Data.T32Chain.strongGenerators Data.T32Chain.base = [32, 8, 2] := by
  have h := small_ok (nb := 3) (F := tFF) (FI := tFI) (B := tBB) (LEN := tLEN) (Mr := tMr)
    (IDX := tIDX) (PTS := tPTS) (POS := tPOS) (PAR := tPAR) (LAB := tLAB) Data.T32Chain rfl rfl
    (by decide) (by decide) rfl (fun _ _ => rfl) (by decide) tSmall_ok
    (sch_of tAll (by norm_num) (by norm_num) fun i hi => by interval_cases i <;> decide)
    (by decide)
    (fun j hj => by
      unfold peq
      rw [CertificateChecks.KernelSpor.ON5K.allBelowN_eq]
      revert j
      decide +kernel)
  exact ⟨h.1, h.2.trans rfl⟩

theorem m_ok : smallChainOK 120 Data.M120Chain = true ∧
    cOrbitSizes 120 Data.M120Chain.strongGenerators Data.M120Chain.base = [120, 56, 6] := by
  have h := small_ok (nb := 3) (F := mFF) (FI := mFI) (B := mBB) (LEN := mLEN) (Mr := mMr)
    (IDX := mIDX) (PTS := mPTS) (POS := mPOS) (PAR := mPAR) (LAB := mLAB) Data.M120Chain rfl rfl
    (by decide) (by decide) rfl (fun _ _ => rfl) (by decide) mSmall_ok
    (sch_of mAll (by norm_num) (by norm_num) fun i hi => by interval_cases i <;> decide)
    (by decide)
    (fun j hj => by
      unfold peq
      rw [CertificateChecks.KernelSpor.ON5K.allBelowN_eq]
      revert j
      decide +kernel)
  exact ⟨h.1, h.2.trans rfl⟩

theorem l_ok : smallChainOK 120 Data.L120Chain = true ∧
    cOrbitSizes 120 Data.L120Chain.strongGenerators Data.L120Chain.base = [120, 56, 3] := by
  have h := small_ok (nb := 3) (F := lFF) (FI := lFI) (B := lBB) (LEN := lLEN) (Mr := lMr)
    (IDX := lIDX) (PTS := lPTS) (POS := lPOS) (PAR := lPAR) (LAB := lLAB) Data.L120Chain rfl rfl
    (by decide) (by decide) rfl (fun _ _ => rfl) (by decide) lSmall_ok
    (sch_of lAll (by norm_num) (by norm_num) fun i hi => by interval_cases i <;> decide)
    (by decide)
    (fun j hj => by
      unfold peq
      rw [CertificateChecks.KernelSpor.ON5K.allBelowN_eq]
      revert j
      decide +kernel)
  exact ⟨h.1, h.2.trans rfl⟩

theorem p_ok : smallChainOK 21 Data.PSL21Chain = true ∧
    cOrbitSizes 21 Data.PSL21Chain.strongGenerators Data.PSL21Chain.base = [21, 20, 16, 3] := by
  have h := small_ok (nb := 4) (F := pFF) (FI := pFI) (B := pBB) (LEN := pLEN) (Mr := pMr)
    (IDX := pIDX) (PTS := pPTS) (POS := pPOS) (PAR := pPAR) (LAB := pLAB) Data.PSL21Chain rfl rfl
    (by decide) (by decide) rfl (fun _ _ => rfl) (by decide) pSmall_ok
    (sch_of pAll (by norm_num) (by norm_num) fun i hi => by interval_cases i <;> decide)
    (by decide)
    (fun j hj => by
      unfold peq
      rw [CertificateChecks.KernelSpor.ON5K.allBelowN_eq]
      revert j
      decide +kernel)
  exact ⟨h.1, h.2.trans rfl⟩

theorem q_ok : smallChainOK 120 Data.PSL120Chain = true ∧
    cOrbitSizes 120 Data.PSL120Chain.strongGenerators Data.PSL120Chain.base = [120, 21, 8] := by
  have h := small_ok (nb := 3) (F := qFF) (FI := qFI) (B := qBB) (LEN := qLEN) (Mr := qMr)
    (IDX := qIDX) (PTS := qPTS) (POS := qPOS) (PAR := qPAR) (LAB := qLAB) Data.PSL120Chain rfl rfl
    (by decide) (by decide) rfl (fun _ _ => rfl) (by decide) qSmall_ok
    (sch_of qAll (by norm_num) (by norm_num) fun i hi => by interval_cases i <;> decide)
    (by decide)
    (fun j hj => by
      unfold peq
      rw [CertificateChecks.KernelSpor.ON5K.allBelowN_eq]
      revert j
      decide +kernel)
  exact ⟨h.1, h.2.trans rfl⟩

open Certificates in
open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native in
theorem facts2215 : smallChainOK 32 Data.T32Chain = true ∧ smallChainOK 120 Data.M120Chain = true ∧
    smallChainOK 120 Data.L120Chain = true ∧ smallChainOK 21 Data.PSL21Chain = true ∧
    smallChainOK 120 Data.PSL120Chain = true ∧
    cOrbitSizes 32 Data.T32Chain.strongGenerators Data.T32Chain.base = [32, 8, 2] ∧
    cOrbitSizes 120 Data.M120Chain.strongGenerators Data.M120Chain.base = [120, 56, 6] ∧
    cOrbitSizes 120 Data.L120Chain.strongGenerators Data.L120Chain.base = [120, 56, 3] ∧
    cOrbitSizes 21 Data.PSL21Chain.strongGenerators Data.PSL21Chain.base = [21, 20, 16, 3] ∧
    cOrbitSizes 120 Data.PSL120Chain.strongGenerators Data.PSL120Chain.base =
      [120, 21, 8] :=
  ⟨t_ok.1, m_ok.1, l_ok.1, p_ok.1, q_ok.1, t_ok.2, m_ok.2, l_ok.2, p_ok.2, q_ok.2⟩

end CertificateChecks.KernelSpor.ON6K

end
