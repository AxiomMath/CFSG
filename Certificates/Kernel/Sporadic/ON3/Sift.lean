
module

public import Certificates.Kernel.Sporadic.ON3.Strong
public import Certificates.Kernel.Sporadic.ON3.Lv
public import Certificates.Kernel.Sporadic.ON3.LvM1
public import Certificates.Kernel.Sporadic.ON3.LvL1
public import CFSG.Certificates.Kernel.Spor.ChainKProof

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON3.posAll CertificateChecks.KernelSpor.ON3.posS 72
#kon_join CertificateChecks.KernelSpor.ON3.ptT0All CertificateChecks.KernelSpor.ON3.ptT0 8
#kon_join CertificateChecks.KernelSpor.ON3.ptT1All CertificateChecks.KernelSpor.ON3.ptT1 1
#kon_join CertificateChecks.KernelSpor.ON3.ptT2All CertificateChecks.KernelSpor.ON3.ptT2 1
#kon_join CertificateChecks.KernelSpor.ON3.ptM0All CertificateChecks.KernelSpor.ON3.ptM0 15
#kon_join CertificateChecks.KernelSpor.ON3.ptM1All CertificateChecks.KernelSpor.ON3.ptM1 42
#kon_join CertificateChecks.KernelSpor.ON3.ptM2All CertificateChecks.KernelSpor.ON3.ptM2 1
#kon_join CertificateChecks.KernelSpor.ON3.ptL0All CertificateChecks.KernelSpor.ON3.ptL0 15
#kon_join CertificateChecks.KernelSpor.ON3.ptL1All CertificateChecks.KernelSpor.ON3.ptL1 21
#kon_join CertificateChecks.KernelSpor.ON3.ptL2All CertificateChecks.KernelSpor.ON3.ptL2 1

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.KS.CH CFSG.ONSchreier CFSG.ONSchreier.Native

theorem pt_of {n m r NS : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    {F : Nat → Bool} (hF : ∀ s < NS, F s = true)
    (hd : ∀ s, F s = cbPtRange n m r STEP PTS POS PAR LAB (Nat.mul s 16) 16) (hm : m ≤ NS * 16) :
    ∀ k < m, cbPt n m r STEP PTS POS PAR LAB k = true := by
  intro k hk
  have hs := hF (k / 16) (by omega)
  rw [hd] at hs
  unfold cbPtRange at hs
  have h := allBlk_spec hs (k % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (k / 16) 16) (k % 16) = k := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h
  have hk' : Nat.blt k m = true := blt_of hk
  rw [hk'] at h
  exact h

theorem posS_eq (s v : Nat) (hs : s < 8) : posS (s + 8 * v) =
    bIf(Nat.beq (Nat.div v 3) 0, posC (tMr (Nat.mod v 3)) (tPTS (Nat.mod v 3)) (tPOS (Nat.mod v 3)) s,
      bIf(Nat.beq (Nat.div v 3) 1, posC (mMr (Nat.mod v 3)) (mPTS (Nat.mod v 3)) (mPOS (Nat.mod v 3)) s,
        posC (lMr (Nat.mod v 3)) (lPTS (Nat.mod v 3)) (lPOS (Nat.mod v 3)) s)) := by
  unfold posS
  simp only [strictB_eq'']
  have e1 : Nat.mod (s + 8 * v) 8 = s := by
    change (s + 8 * v) % 8 = s
    omega
  have e2 : Nat.div (s + 8 * v) 8 = v := by
    change (s + 8 * v) / 8 = v
    omega
  rw [e1, e2]

theorem pos_of {m : Nat} {PTS POS : Nat → Nat} (h : ∀ s < 8, posC m PTS POS s = true) :
    ∀ z < 245520, cbPos 245520 m PTS POS z = true := by
  intro z hz
  have h' := allN_spec (h (z / 30690) (by omega)) (z % 30690) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (z / 30690) 30690) (z % 30690) = z := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h'
  exact h'

theorem pos_v {v : Nat} (hv : v < 9) {s : Nat} (hs : s < 8) : posS (s + 8 * v) = true := by
  have h : s + 8 * v < 72 := by omega
  exact posAll _ h

theorem posT_all {i : Nat} (hi : i < 3) :
    ∀ z < 245520, cbPos 245520 (tMr i) (tPTS i) (tPOS i) z = true := by
  apply pos_of
  intro s hs
  have h := pos_v (v := i) (by omega) hs
  rw [posS_eq _ _ hs] at h
  interval_cases i <;> exact h

theorem posM_all {i : Nat} (hi : i < 3) :
    ∀ z < 245520, cbPos 245520 (mMr i) (mPTS i) (mPOS i) z = true := by
  apply pos_of
  intro s hs
  have h := pos_v (v := i + 3) (by omega) hs
  rw [posS_eq _ _ hs] at h
  interval_cases i <;> exact h

theorem posL_all {i : Nat} (hi : i < 3) :
    ∀ z < 245520, cbPos 245520 (lMr i) (lPTS i) (lPOS i) z = true := by
  apply pos_of
  intro s hs
  have h := pos_v (v := i + 6) (by omega) hs
  rw [posS_eq _ _ hs] at h
  interval_cases i <;> exact h

theorem sizes : tMr 0 = 128 ∧ tMr 1 = 4 ∧ tMr 2 = 1 ∧ mMr 0 = 240 ∧ mMr 1 = 672 ∧ mMr 2 = 1 ∧
    lMr 0 = 240 ∧ lMr 1 = 336 ∧ lMr 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem ptT_all {i : Nat} (hi : i < 3) : ∀ k < tMr i, cbPt 245520 (tMr i) (Nat.mul 2 (tLEN i))
    (stepX tF tFI (tIDX i) (tLEN i)) (tPTS i) (tPOS i) (tPAR i) (tLAB i) k = true := by
  obtain ⟨s0, s1, s2, -⟩ := sizes
  interval_cases i
  · exact pt_of ptT0All (fun _ => rfl) (Nat.le_trans (Nat.le_of_eq s0) (by decide))
  · exact pt_of ptT1All (fun _ => rfl) (Nat.le_trans (Nat.le_of_eq s1) (by decide))
  · exact pt_of ptT2All (fun _ => rfl) (Nat.le_trans (Nat.le_of_eq s2) (by decide))

theorem ptM_all {i : Nat} (hi : i < 3) : ∀ k < mMr i, cbPt 245520 (mMr i) (Nat.mul 2 (mLEN i))
    (stepX mF mFI (mIDX i) (mLEN i)) (mPTS i) (mPOS i) (mPAR i) (mLAB i) k = true := by
  obtain ⟨-, -, -, s0, s1, s2, -⟩ := sizes
  interval_cases i
  · exact pt_of ptM0All (fun _ => rfl) (Nat.le_trans (Nat.le_of_eq s0) (by decide))
  · exact pt_of ptM1All (fun _ => rfl) (Nat.le_trans (Nat.le_of_eq s1) (by decide))
  · exact pt_of ptM2All (fun _ => rfl) (Nat.le_trans (Nat.le_of_eq s2) (by decide))

theorem ptL_all {i : Nat} (hi : i < 3) : ∀ k < lMr i, cbPt 245520 (lMr i) (Nat.mul 2 (lLEN i))
    (stepX lF lFI (lIDX i) (lLEN i)) (lPTS i) (lPOS i) (lPAR i) (lLAB i) k = true := by
  obtain ⟨-, -, -, -, -, -, s0, s1, s2⟩ := sizes
  interval_cases i
  · exact pt_of ptL0All (fun _ => rfl) (Nat.le_trans (Nat.le_of_eq s0) (by decide))
  · exact pt_of ptL1All (fun _ => rfl) (Nat.le_trans (Nat.le_of_eq s1) (by decide))
  · exact pt_of ptL2All (fun _ => rfl) (Nat.le_trans (Nat.le_of_eq s2) (by decide))

theorem heads {i : Nat} (hi : i < 3) : idxOK tF 8 bB i (tIDX i) (tLEN i) = true ∧
    idxOK mF 5 bB i (mIDX i) (mLEN i) = true ∧ idxOK lF 4 bB i (lIDX i) (lLEN i) = true ∧
    cbHead 245520 (tMr i) (bB i) (tPTS i) (tPAR i) (tLAB i) = true ∧
    cbHead 245520 (mMr i) (bB i) (mPTS i) (mPAR i) (mLAB i) = true ∧
    cbHead 245520 (lMr i) (bB i) (lPTS i) (lPAR i) (lLAB i) = true := by
  have h := allN_spec heads_ok i hi
  simp only [bAnd_iff] at h
  exact h

theorem base_facts : Data.TChain.base.size = 3 ∧ ∀ k < 3, Data.TChain.base[k]! = bB k ∧ bB k < 245520 := by
  refine ⟨rfl, fun k hk => ?_⟩
  interval_cases k <;> exact ⟨rfl, by decide⟩

theorem strong_facts {S : Array (Array Nat)} {s : Nat} {F FI : Nat → Nat → Nat}
    (hS : S.size = s ∧ ∀ j < s, S[j]! = Array.ofFn (n := 245520) fun i => F j i.val)
    (hp : InvPair 245520 s F FI) : ∀ j < s, ∀ x < 245520,
      (S[j]!)[x]! = F j x ∧ F j x < 245520 ∧ FI j x < 245520 ∧ FI j (F j x) = x := by
  intro j hj x hx
  rw [hS.2 j hj, CFSG.KS.PW.ofFn_get' (f := F j) hx]
  exact ⟨rfl, (hp j hj x hx).1, (hp j hj x hx).2.1, (hp j hj x hx).2.2.1⟩

theorem memT {g : Array Nat} {G : Nat → Nat} (hg : ∀ k < 3, g[bB k]! = G (bB k))
    (hG : ∀ k < 3, G (bB k) < 245520) (hs : siftT G = true) :
    memIn TStrong Data.TChain.base g = true := by
  unfold memIn
  exact memIn3_proved (B := bB) (G := fun k => G (bB k)) tStrong_get.1
    (fun j hj => by rw [tStrong_get.2 j hj, Array.size_ofFn])
    (strong_facts tStrong_get tF_pair) base_facts.1 base_facts.2 hg hG (by decide)
    (fun i hi => (heads hi).1) (fun i hi => (heads hi).2.2.2.1) (fun i hi => ptT_all hi)
    (fun i hi => posT_all hi) hs

theorem memM {g : Array Nat} {G : Nat → Nat} (hg : ∀ k < 3, g[bB k]! = G (bB k))
    (hG : ∀ k < 3, G (bB k) < 245520) (hs : siftM G = true) :
    memIn MStrong Data.MChain.base g = true := by
  unfold memIn
  exact memIn3_proved (B := bB) (G := fun k => G (bB k)) mStrong_get.1
    (fun j hj => by rw [mStrong_get.2 j hj, Array.size_ofFn])
    (strong_facts mStrong_get mF_pair) base_facts.1 base_facts.2 hg hG (by decide)
    (fun i hi => (heads hi).2.1) (fun i hi => (heads hi).2.2.2.2.1) (fun i hi => ptM_all hi)
    (fun i hi => posM_all hi) hs

theorem memL {g : Array Nat} {G : Nat → Nat} (hg : ∀ k < 3, g[bB k]! = G (bB k))
    (hG : ∀ k < 3, G (bB k) < 245520) (hs : siftL G = true) :
    memIn LStrong Data.LChain.base g = true := by
  unfold memIn
  exact memIn3_proved (B := bB) (G := fun k => G (bB k)) lStrong_get.1
    (fun j hj => by rw [lStrong_get.2 j hj, Array.size_ofFn])
    (strong_facts lStrong_get lF_pair) base_facts.1 base_facts.2 hg hG (by decide)
    (fun i hi => (heads hi).2.2.1) (fun i hi => (heads hi).2.2.2.2.2) (fun i hi => ptL_all hi)
    (fun i hi => posL_all hi) hs

theorem sifts : siftT ZT = true ∧ siftL QT = true ∧ siftM L1T = true ∧ siftM L2T = true ∧
    ∀ j < 4, siftM (DT j) = true ∧ siftM (fun x => CIT (DT j (CT x))) = true := by
  have h := sifts_ok
  unfold siftsOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun j hj => ?_⟩
  have h' := allN_spec h5 j hj
  simp only [bAnd_iff] at h'
  exact h'

end CertificateChecks.KernelSpor.ON3

end
