module

public import Certificates.Kernel.Fi23Nt.GlueBase
public import Certificates.Kernel.Fi23Nt.Enum
public import Certificates.Kernel.Fi23Nt.Tab
public import Certificates.Kernel.Fi23Nt.FixB
public import Certificates.Kernel.Fi23Nt.DD
public import Certificates.Kernel.Fi23Nt.Misc
public import Certificates.Kernel.Fi23Nt.FixQ
public import Certificates.Kernel.Fi23Nt.Pos
public import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S3Asch
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118T
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.Sporadic.Co2Smith.Defs
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import Certificates.Certificate13622Base

public section

namespace CertificateChecks.KernelFi23Nt

open CFSG.Sporadic.Fi23 CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.KC.Fi23Nt
  CFSG.KC.Fi23R CertificateChecks.KernelFi23Q CFSG.KS.Fi23Nt CFSG.KS.E27Lie
  CFSG.HardMathSupport.Foote.E27 CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist CFSG.KD.Fi23Nt
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open Subgroup (centralizer closure)

#kc_forall_tree eb_all (fun s => CFSG.KD.Fi23Nt.enumBSl s = true) 9 CFSG.KD.Fi23Nt.tw101701eb
#kc_forall_tree sb_all (fun s => CFSG.KD.Fi23Nt.subBSl s = true) 9 CFSG.KD.Fi23Nt.tw101701sb
#kc_forall_tree db_all (fun s => CFSG.KD.Fi23Nt.cosBSl s = true) 9 CFSG.KD.Fi23Nt.tw101701db
#kc_forall_tree x_all (fun s => CFSG.KD.Fi23Nt.fixSl s = true) 31 CFSG.KD.Fi23Nt.tw101701x
#kc_forall_tree d_all (fun s => CFSG.KD.Fi23Nt.ddSl s = true) 31 CFSG.KD.Fi23Nt.tw101701d

theorem words : wsokK eBW = true ∧ wsokK eCW = true ∧ wsokK ePW = true ∧ wsokK fixW = true ∧
    wsokK (fstK st) = true ∧ wsokK ddW = true ∧ wokK hW = true ∧ wsokK yW = true ∧
      wsokK bW = true := by
  have h := tw101701wk
  unfold CFSG.KD.Fi23Nt.wordsOK at h
  simp only [CFSG.KS.bAnd_iff] at h
  exact h

theorem wok_nil : WOK [] := fun _ h => absurd h List.not_mem_nil


noncomputable abbrev gB (j : ℕ) : CFSG.Sporadic.Fi23.J := wE (eBW.getD j [])

theorem tabB : TabData gB (parT eBN eBPar) (ltT eBN eBLt) eBN 3 := by
  have he : ∀ i < eBN, enumIK G eBW 3 eBN eBPar eBImg eBLt i = true := fun i hi =>
    all_of_blk (f := enumIK G eBW 3 eBN eBPar eBImg eBLt) (b := 81) (c := 9) (by norm_num)
      (fun s hs => eb_all s hs) i (by change i < 729 at hi; omega)
  exact (enum_sound (W := eBW) (m := 3) (n := eBN) (PAR := eBPar) (IMG := eBImg) (ORD := eBOrd)
    (LT := eBLt) (by norm_num) (fun j _ => getD_mem_of eBW (woks_of words.1) wok_nil j)
    (by change 0 < 729; norm_num) he tw101701ob).1

theorem factB_k : FactB := by
  have hBW : ∀ w ∈ eBW, WOK w := woks_of words.1
  have hT := tabB
  have hn : 0 < eBN := by change 0 < 729; norm_num
  obtain ⟨Q, hQ, hQcl⟩ := hT.exists_subgroup hn
  have hQc : Nat.card Q = 729 := hT.card_subgroup hQ
  have hgQ : ∀ j < 3, gB j ∈ Q := fun j hj => by
    rw [hQcl]
    exact Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩
  have hh : subHK eBN tBA = true := tw101701hb
  have hs : ∀ k < 81, subIK eBN eBPar eBLt tBA (mskK tBA) k = true := fun k hk =>
    all_of_blk (f := subIK eBN eBPar eBLt tBA (mskK tBA)) (b := 9) (c := 9) (by norm_num)
      (fun s hs => by
        have h := sb_all s hs
        unfold subBSl subSlOf at h
        rwa [sB_eq] at h) k (by omega)
  obtain ⟨A₀, hA, hAc, hAcomm, -⟩ := sub_group hT hh hs
  have hlt := (subHK_spec hh).2.1
  have hA₀Q : A₀ ≤ Q := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := (hA x).1 hx
    exact (hQ _).2 ⟨_, hlt k hk, rfl⟩
  have hc : ∀ x < eBN, cosIK eBN eBPar eBLt tBA tBR tBNr tBD x = true := fun x hx =>
    all_of_blk (f := cosIK eBN eBPar eBLt tBA tBR tBNr tBD) (b := 81) (c := 9) (by norm_num)
      (fun s hs => db_all s hs) x (by change x < 729 at hx; omega)
  have hz : ∀ c < tBNr, centIK eBN eBPar eBLt tBA 10 (lnK 16 tBR c) = true :=
    CFSG.KS.allN_spec tw101701nb
  have hcent : ∀ x ∈ Q, x ∉ A₀ → Nat.card ↥(A₀ ⊓ centralizer ({x} : Set J)) ≤ 9 := by
    intro x hx hxA
    obtain ⟨i, hi, rfl⟩ := (hQ x).1 hx
    have := cent_lt hT hh hs hA hc hz i hi hxA
    omega
  have hZ : Nat.card ↥(A₀ ⊓ centralizer (Q : Set J)) < 9 := by
    have h1 : Nat.card ↥(A₀ ⊓ centralizer (Set.range fun j : Fin 3 => gB j)) < 4 :=
      z_lt hT hn hh hA tw101701zb
    have h2 : A₀ ⊓ centralizer (Q : Set J) ≤
        A₀ ⊓ centralizer (Set.range fun j : Fin 3 => gB j) :=
      inf_le_inf_left _ (Subgroup.centralizer_le (by rw [hQcl]; exact Subgroup.subset_closure))
    have := Subgroup.card_le_of_le h2
    omega
  have hQdd : Q ≤ centralizer ({d} : Set J) ⊓ centralizer ({d1} : Set J) := by
    rw [hQcl, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact getD_mem_of (P := fun w => wE w ∈ centralizer ({d} : Set J) ⊓ centralizer ({d1} : Set J))
      eBW (fixQ_spec hBW tw101701fq) (one_mem _) j
  have hfix : ∀ p < 31671, A₀ ≤ centralizer ({conjPt p} : Set J) → p ∈ fixF := by
    intro p hp hAp
    obtain ⟨h1, h2, h3⟩ := slice_of hp
    have hl : lnkUK eBW eBPar eBN tBA (fun v => v) fixIdx fixW = true := tw101701lb
    have hlk := lnk_spec fixIdx fixW hl
    have hsl : fixSlK G fixF fixW (Nat.mul (p / 1024) 1024) (slLen (p / 1024)) = true :=
      x_all _ h1
    refine fix_spec (woks_of words.2.2.2.1) hsl (by change p / 1024 * 1024 ≤ p; omega)
      (by change p < p / 1024 * 1024 + slLen (p / 1024); omega) hp ?_
    intro w hw
    obtain ⟨i, -, hi, ⟨k, hk, hik⟩, hw'⟩ := forall2_mem hlk w hw
    simp only [hw']
    have e : wE (wdK eBW eBPar eBN i) = tabElt gB (parT eBN eBPar) i :=
      wd_prod hT regE (fun _ _ => rfl) eBN i hi.le hi
    rw [e]
    exact (mem_centralizer_conjPt_iff _ hp).1 (hAp ((hA _).2 ⟨k, hk, by rw [hik]⟩))
  have hpair := pair_of (by decide +kernel) (by decide +kernel) tw101701pr
  have hDW : ∀ w ∈ ddW, WOK w := woks_of words.2.2.2.2.2.1
  have hdw := tw101701dw
  unfold CFSG.KD.Fi23Nt.ddWOK at hdw
  simp only [CFSG.KS.bAnd_iff] at hdw
  obtain ⟨e0, e1, e2, e3⟩ := hdw
  have w0 : wE (ddW.getD 0 []) = gB 0 := by rw [eqLK_eq _ _ e0]
  have w1 : wE (ddW.getD 1 []) = gB 1 := by rw [eqLK_eq _ _ e1]
  have w2 : wE (ddW.getD 2 []) = gB 2 * gB 0 := by rw [eqLK_eq _ _ e2, appK_eq, wE_append]
  have w3 : wE (ddW.getD 3 []) = gB 2 * gB 2 := by rw [eqLK_eq _ _ e3, appK_eq, wE_append]
  have hstab : ∀ k < 31671, k ≠ 0 → k ≠ 1 → conjPt k * d = d * conjPt k →
      conjPt k * d1 = d1 * conjPt k →
      ∃ f : Fin 4 → J, (∀ i, f i ∈ Q) ∧ Function.Injective fun i => idx 31671 (f i) k := by
    intro k hk hk0 hk1 hkd hkd1
    have hd : idx 31671 d k = k := (mem_centralizer_conjPt_iff d hk).1
      (Subgroup.mem_centralizer_iff.2 fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hkd)
    have hd1 : idx 31671 d1 k = k := (mem_centralizer_conjPt_iff d1 hk).1
      (Subgroup.mem_centralizer_iff.2 fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hkd1)
    have t0 : tA G 0 k = k := by rw [tA_eq (by norm_num) hk, conjPt_zero, hd]
    have t1 : tA G 1 k = k := by
      rw [tA_eq (by norm_num) hk]
      exact hd1
    have hb : Nat.ble k 1 = false := Bool.eq_false_iff.2 fun h => by
      have := Nat.le_of_ble_eq_true h
      omega
    have hdd := all_of_slices (f := fun v => bIf(Nat.ble v 1, true, bIf(Nat.beq (tA G 0 v) v,
      bIf(Nat.beq (tA G 1 v) v, dd4K G ddW v, true), true))) (fun s hs => d_all s hs) hk
    beta_reduce at hdd
    rw [hb, beq_true t0, beq_true t1] at hdd
    have h4 : dd4K G ddW k = true := hdd
    unfold dd4K at h4
    simp only [sB_eq] at h4
    have hc4 := Nat.le_of_ble_eq_true h4
    rw [cnt5_card] at hc4
    have hv : ∀ j, wv G (ddW.getD j []) k = idx 31671 (wE (ddW.getD j [])) k := fun j =>
      wv_eq (getD_mem_of ddW hDW wok_nil j) hk
    rw [hv, hv, hv, hv, w0, w1, w2, w3] at hc4
    refine exists_four _ hc4 fun s hs => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, mul_mem (hgQ 2 (by norm_num)) (hgQ 2 (by norm_num)), rfl⟩
    · exact ⟨_, mul_mem (hgQ 2 (by norm_num)) (hgQ 0 (by norm_num)), rfl⟩
    · exact ⟨_, hgQ 1 (by norm_num), rfl⟩
    · exact ⟨_, hgQ 0 (by norm_num), rfl⟩
    · exact ⟨1, one_mem _, idx_one _⟩
  exact factB_of_math fixF hQdd hQc hA₀Q hAcomm hAc hcent hZ hfix hpair hstab

end CertificateChecks.KernelFi23Nt

end
