
module

public import Certificates.Kernel.Misc.RuBigZ.Glue
public import Certificates.Kernel.Misc.RuBigZ.L0
public import Certificates.Kernel.Misc.RuBigZ.E0
public import Certificates.Kernel.Misc.RuBigZ.E1
public import Certificates.Kernel.Misc.RuBigZ.E3
public import Certificates.Kernel.Misc.RuBigZ.E5
public import Certificates.Kernel.Misc.RuBigZ.Fix
public import CFSG.Certificates.Kernel.Misc.RuBigZElSound
public import CFSG.Quasithin.Vol2.KGFactC31RuRefDefs
public import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuCentralizer
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelMisc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.RuInv
  CFSG.KC.Misc.RuInv.P CFSG.KC.Misc.RuScan CFSG.KC.Misc.RuBigZ
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelMisc.RuScan CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Ru CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier

#kc_forall_tree l0All (fun q => ch7233l0_ q = true) 4 CertificateChecks.KernelMisc.RuBigZ.ch7233l0_
#kc_forall_tree e0All (fun q => ch7233e0_ q = true) 16 CertificateChecks.KernelMisc.RuBigZ.ch7233e0_
#kc_forall_tree e1All (fun q => ch7233e1_ q = true) 2 CertificateChecks.KernelMisc.RuBigZ.ch7233e1_
#kc_forall_tree e2All (fun q => ch7233e2_ q = true) 4 CertificateChecks.KernelMisc.RuBigZ.ch7233e2_
#kc_forall_tree e3All (fun q => ch7233e3_ q = true) 4 CertificateChecks.KernelMisc.RuBigZ.ch7233e3_
#kc_forall_tree e4All (fun q => ch7233e4_ q = true) 2 CertificateChecks.KernelMisc.RuBigZ.ch7233e4_
#kc_forall_tree e5All (fun q => ch7233e5_ q = true) 8 CertificateChecks.KernelMisc.RuBigZ.ch7233e5_

theorem c0R : rcnt (RuCS.LR 0) = 1920 := Nat.eq_of_beq_eq_true RuCNF.cC0
theorem c1R : rcnt (RuCS.LR 1) = 64 := Nat.eq_of_beq_eq_true RuCNF.cC1
theorem c2R : rcnt (RuCS.LR 2) = 2 := Nat.eq_of_beq_eq_true RuCNF.cC2

theorem ptR_y3 {t0 t1 t2 : Nat} {g₀ g₁ g₂ : Equiv.Perm (Fin 4060)} (P0 : PRep 4060 12 t0 g₀)
    (P1 : PRep 4060 12 t1 g₁) (P2 : PRep 4060 12 t2 g₂) :
    PtR (yAp [t0, t1, t2]) (g₀ * g₁ * g₂) := fun x => by
  rw [yAp_eq (gs := [g₀, g₁, g₂]) (.cons P0 (.cons P1 (.cons P2 .nil))) x]
  simp [mul_assoc]

theorem ptR_y2 {t1 t2 : Nat} {g₁ g₂ : Equiv.Perm (Fin 4060)} (P1 : PRep 4060 12 t1 g₁)
    (P2 : PRep 4060 12 t2 g₂) : PtR (yAp [t1, t2]) (g₁ * g₂) := fun x => by
  rw [yAp_eq (gs := [g₁, g₂]) (.cons P1 (.cons P2 .nil)) x]
  simp

theorem comm_pt {f F : Nat → Nat} {g h : Equiv.Perm (Fin 4060)} (hf : PtR f g) (hF : PtR F h)
    (hc : g * h = h * g) (p : Fin 4060) : f (F p) = F (f p) := by
  have e := congrArg (fun q : Equiv.Perm (Fin 4060) => (q p : Nat)) hc
  simp only [Equiv.Perm.mul_apply] at e
  rw [hF p, hf (h p), hf p, hF (g p)]
  exact e

theorem fix_s {j : Nat} (hj : j < 128) {g₁ g₂ : Equiv.Perm (Fin 4060)}
    (P1 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 1) + j / 2)) g₁)
    (P2 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 2) + j % 2)) g₂) : (g₁ * g₂) 0 = 0 := by
  have hf := ch7233fx_ok
  rw [Bool.and_eq_true] at hf
  have h1 := fixL_sound hf.1 (k := j / 2) (by rw [c1R]; omega)
  have h2 := fixL_sound hf.2 (k := j % 2) (by rw [c2R]; omega)
  have e1 : g₁ 0 = 0 := Fin.ext ((apP_eq P1 0).symm.trans h1)
  have e2 : g₂ 0 = 0 := Fin.ext ((apP_eq P2 0).symm.trans h2)
  rw [Equiv.Perm.mul_apply, e2, e1]

theorem prune_ne {t u1 u2 V B : Nat} {g₀ g₁ g₂ bv bb : Equiv.Perm (Fin 4060)}
    (P0 : PRep 4060 12 t g₀) (P1 : PRep 4060 12 u1 g₁) (P2 : PRep 4060 12 u2 g₂)
    (hV : PtR (apP V) bv) (hB : PtR (apP B) bb) (key : g₀⁻¹ (bb (g₀ 0)) = (g₁ * g₂) (bv 0))
    {r : Nat} (hr : r < 4060) (he : apP t r = apP B (apP t 0))
    (hn : yAp [u1, u2] (apP V 0) ≠ r) : False := by
  have e0 : apP t 0 = (g₀ 0 : Nat) := apP_eq P0 0
  have er : apP t r = (g₀ ⟨r, hr⟩ : Nat) := apP_eq P0 ⟨r, hr⟩
  rw [er, e0, hB (g₀ 0)] at he
  have hg : g₀ ⟨r, hr⟩ = bb (g₀ 0) := Fin.ext he
  have key' : (⟨r, hr⟩ : Fin 4060) = (g₁ * g₂) (bv 0) := by
    rw [← key, ← hg, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  apply hn
  have ev : apP V 0 = (bv 0 : Nat) := hV 0
  rw [ev, ptR_y2 P1 P2 (bv 0), ← key']

section Glue

theorem ruC_decomp {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruC) :
    ∃ a < 1920, ∃ j < 128, ∃ g₀ g₁ g₂ : Equiv.Perm (Fin 4060),
      PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 0) + a)) g₀ ∧
      PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 1) + j / 2)) g₁ ∧
      PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 2) + j % 2)) g₂ ∧ g = g₀ * g₁ * g₂ := by
  have hA : ChainArrays ruChainC ((ruField4060 1).extract 0 2) (ruField4060 1)
      (ruBaseArr 4060 ruCBase) (ruWordsArr 2 7 ruCDerivations) := ruChain_arrays ruChainC_check.1
  have hcC : g ∈ ruChainC.originalSubgroup := by rw [ruChainC_sub]; exact hg
  have hm := mem_products_of_mem hA (by norm_num) ruChainC_check.1 hcC
  rw [show ruChainC.baseCount = 3 from rfl] at hm
  obtain ⟨i, hi, g₀, g₁, g₂, P0, P1, P2, rfl⟩ := enum3 RuCNF.bindsC RuCNF.pC RuCS.hl hm
  rw [c0R, c1R, c2R] at hi
  rw [c1R, c2R] at P0 P1
  rw [c2R] at P2
  refine ⟨i / 2 / 64, by omega, i % 128, by omega, g₀, g₁, g₂, P0, ?_, ?_, rfl⟩
  · rw [(by omega : i % 128 / 2 = i / 2 % 64)]
    exact P1
  · rw [(by omega : i % 128 % 2 = i % 2)]
    exact P2

theorem cent_ne {ws : List (List Int)} {r o : Nat}
    (hP : ∀ i < r, PtR (apP (R (o + i))) (wG (ws.getD i []))) {a j : Nat} (hj : j < 128)
    {g₀ g₁ g₂ : Equiv.Perm (Fin 4060)}
    (P0 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 0) + a)) g₀)
    (P1 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 1) + j / 2)) g₁)
    (P2 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 2) + j % 2)) g₂)
    {k : Nat} (hk : k < r) {rr : Nat} (hr : rr < 4060)
    (he : apP (RuCS.TR (roff 4060 48720 (RuCS.LR 0) + a)) rr =
      apP (R (o + k)) (apP (RuCS.TR (roff 4060 48720 (RuCS.LR 0) + a)) 0))
    (hn : notIn (orbM RuCS.LR RuCS.TR (R (o + k))) rr = true) :
    ¬ CentB (vOf ws r) (g₀ * g₁ * g₂) := by
  intro hc
  have hc' : g₀ * (g₁ * g₂) * wG (ws.getD k []) = wG (ws.getD k []) * (g₀ * (g₁ * g₂)) := by
    have := hc ⟨k, hk⟩
    rw [mul_assoc g₀] at this
    exact this
  exact prune_ne P0 P1 P2 (hP k hk) (hP k hk) (prune (fix_s hj P1 P2) hc') hr he
    (orbM_sound hn (by rw [c1R]; omega) (by rw [c2R]; omega))

theorem norm_ne {a j : Nat} (hj : j < 128) {g₀ g₁ g₂ : Equiv.Perm (Fin 4060)}
    (P0 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 0) + a)) g₀)
    (P1 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 1) + j / 2)) g₁)
    (P2 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 2) + j % 2)) g₂)
    {k : Nat} (hk : k < 4)
    (hw : ∀ w < 16, ∃ r < 4060, apP (RuCS.TR (roff 4060 48720 (RuCS.LR 0) + a)) r =
        apP (R (21 + w)) (apP (RuCS.TR (roff 4060 48720 (RuCS.LR 0) + a)) 0) ∧
      notIn (orbM RuCS.LR RuCS.TR (R (12 + k))) r = true) :
    ¬ ∀ i, ∃ d, eElt v16 d = g₀ * g₁ * g₂ * v16 i * (g₀ * g₁ * g₂)⁻¹ := by
  intro hn
  obtain ⟨d, hd⟩ := hn ⟨k, hk⟩
  obtain ⟨m, hm, rfl⟩ := exists_maskVec d
  obtain ⟨rr, hr, he, hno⟩ := hw m hm
  have hW : PtR (apP (R (21 + m)))
      (g₀ * (g₁ * g₂) * wG (basis16W.getD k []) * (g₀ * (g₁ * g₂))⁻¹) := by
    have e : eElt v16 (maskVec 4 m) = mProd (fun i => wG (basis16W.getD i [])) 4 m :=
      (mProd_eq_eElt m (comm_of_eb (v := fun i => wG (basis16W.getD i [])) ebasisK.2.2.2.1)).symm
    have := ptR_apP (prep_RW m hm)
    rw [← e, hd, mul_assoc g₀] at this
    exact this
  exact prune_ne P0 P1 P2 (p16 k hk) hW (prune_norm (fix_s hj P1 P2) rfl) hr he
    (orbM_sound hno (by rw [c1R]; omega) (by rw [c2R]; omega))

theorem not_cent {ws : List (List Int)} {r o : Nat}
    (hP : ∀ i < r, PtR (apP (R (o + i))) (wG (ws.getD i []))) {f : Nat → Nat}
    {g : Equiv.Perm (Fin 4060)} (hf : PtR f g) (h : NcB f R o r) : ¬ CentB (vOf ws r) g := by
  intro hc
  obtain ⟨k, hk, p, hp, hne⟩ := h
  exact hne (comm_pt hf (hP k hk) (hc ⟨k, hk⟩) ⟨p, hp⟩)

theorem not_norm {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hf : PtR f g) {k : Nat}
    (hk : k < 4) {p : Nat} (hp : p < 4060)
    (hne : ∀ w < 16, apP (R (21 + w)) (f p) ≠ f (apP (R (12 + k)) p)) :
    ¬ ∀ i, ∃ d, eElt v16 d = g * v16 i * g⁻¹ := by
  intro hn
  obtain ⟨d, hd⟩ := hn ⟨k, hk⟩
  obtain ⟨m, hm, rfl⟩ := exists_maskVec d
  have hW : PtR (apP (R (21 + m))) (g * wG (basis16W.getD k []) * g⁻¹) := by
    have e : eElt v16 (maskVec 4 m) = mProd (fun i => wG (basis16W.getD i [])) 4 m :=
      (mProd_eq_eElt m (comm_of_eb (v := fun i => wG (basis16W.getD i [])) ebasisK.2.2.2.1)).symm
    have := ptR_apP (prep_RW m hm)
    rw [← e, hd] at this
    exact this
  apply hne m hm
  have e1 : f p = (g ⟨p, hp⟩ : Nat) := hf ⟨p, hp⟩
  have e2 : apP (R (12 + k)) p = (wG (basis16W.getD k []) ⟨p, hp⟩ : Nat) := p16 k hk ⟨p, hp⟩
  rw [e1, e2, hW, hf]
  simp

theorem mem_of_mAp {o r : Nat} {P : Nat → Nat} {ws : List (List Int)}
    (hP : ∀ i < r, PtR (apP (P (o + i))) (wG (ws.getD i []))) (hv : EBasis (vOf ws r))
    {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (hf : PtR f g) {m : Nat}
    (h : ∀ b < 4, f b = mAp P o r m b) : g ∈ refSub (vOf ws r) := by
  have e := eq_of_pts bF hbsJ hg (mProd_mem bF hbsJ (wGv_mem ws) m r) hf (ptR_mAp m hP) h
  rw [refSub_eq hv, e, mProd_eq_eElt m (comm_of_eb (v := fun i => wG (ws.getD i [])) hv)]
  exact eElt_mem hv _

theorem mem_of_orbC {x xi J o : Nat} {P : Nat → Nat} {ws : List (List Int)}
    {xg : Equiv.Perm (Fin 4060)} (hx : PtR (apP x) xg) (hxi : PtR (apP xi) xg⁻¹)
    (hP : ∀ i < 5, PtR (apP (P (o + i))) (wG (ws.getD i []))) (hv : EBasis (vOf ws 5))
    {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (hf : PtR f g)
    (h : OrbC f x xi J P o) (h2 : g * g = 1) (ho : OrbComm xg g J) : g ∈ refSub (vOf ws 5) := by
  rcases h with ⟨p, hp, hne⟩ | ⟨j, hj1, hjJ, p, hp, hne⟩ | ⟨m, -, hb⟩
  · exfalso
    apply hne
    have e : f p = (g ⟨p, hp⟩ : Nat) := hf ⟨p, hp⟩
    rw [e, hf (g ⟨p, hp⟩), ← Equiv.Perm.mul_apply, h2, Equiv.Perm.one_apply]
  · exfalso
    have hX : PtR (xAp x j) (xg ^ j) := ptR_xAp hx j
    have hXI : PtR (xAp xi j) (xg ^ j)⁻¹ := by
      rw [← inv_pow]
      exact ptR_xAp hxi j
    have hH : PtR (fun y => xAp x j (f (xAp xi j y))) (xg ^ j * g * (xg ^ j)⁻¹) :=
      ptR_comp (f := fun y => xAp x j (f y)) (f' := xAp xi j)
        (ptR_comp (f := xAp x j) (f' := f) hX hf) hXI
    have hc := ho (j - 1) (by omega)
    rw [(by omega : j - 1 + 1 = j)] at hc
    exact hne (comm_pt hf hH hc ⟨p, hp⟩)
  · exact mem_of_mAp hP hv hg hf hb

theorem pow_of_twoC {ys : List Nat} {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hf : PtR (yAp ys) g) {E : Nat} (h : TwoC ys E) : g ^ 2 ^ E = 1 := by
  refine bF _ (Subgroup.pow_mem _ hg _) fun x hx => ?_
  obtain ⟨e, he, hb⟩ := h x.val (hbsJ x hx)
  have hfix : (g ^ 2 ^ e) x = x := Fin.ext ((ptR_yPow hf (2 ^ e) x).symm.trans hb)
  have e2 : 2 ^ E = 2 ^ e * 2 ^ (E - e) := by rw [← pow_add, Nat.add_sub_cancel' he]
  rw [e2, pow_mul]
  exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix _

theorem cent_of_g16C {f : Nat → Nat} {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (hf : PtR f g)
    (h : G16C f R (Q 16) (Q 17)) : CentB v16 (g16 * g * g16⁻¹) := by
  intro i
  have hG := ptR_QW (k := 16) (Or.inr (Or.inr (Or.inr rfl)))
  have hF : PtR (fun y => apP (Q 16) (f (apP (Q (16 + 1)) y)))
      (wG (qW 16) * g * (wG (qW 16))⁻¹) :=
    ptR_comp (f := fun y => apP (Q 16) (f y)) (f' := apP (Q (16 + 1)))
      (ptR_comp (f := apP (Q 16)) (f' := f) hG.1 hf) hG.2
  have hm : g16 * g * g16⁻¹ ∈ ruP := ruP.mul_mem (ruP.mul_mem (wG_mem _) hg) (ruP.inv_mem (wG_mem _))
  exact eq_of_pts bF hbsJ (ruP.mul_mem hm (wG_mem _)) (ruP.mul_mem (wG_mem _) hm)
    (ptR_comp hF (p16 i i.2)) (ptR_comp (p16 i i.2) hF) fun b hb => h i i.2 b hb

theorem alive {AL EL : Nat → Nat} {X n : Nat} (hal : alChk RuCS.LR L AL X n = true)
    (hch : ∀ a' < n, elChk RuCS.LR RuCS.TR R Q AL EL X (Nat.mul 32 (a' / 32)) 32 = true)
    {a j : Nat} (ha : a < 1920) (hj : j < 128) (hL : L (21 * a + X) = 1) :
    ∃ rec, elOne [RuCS.TR (roff 4060 48720 (RuCS.LR 0) + a),
      RuCS.TR (roff 4060 48720 (RuCS.LR 1) + j / 2),
      RuCS.TR (roff 4060 48720 (RuCS.LR 2) + j % 2)] R Q X rec = true := by
  obtain ⟨a', ha', hA⟩ := alChk_sound hal a (by rw [c0R]; exact ha) hL
  have h := elChk_sound (hch a' ha') (a := a') (by change 32 * (a' / 32) ≤ a'; omega)
    (by change a' < 32 * (a' / 32) + 32; omega) (j := j) (by rw [c1R, c2R]; omega)
  rw [hA, c2R] at h
  exact ⟨_, h⟩

theorem hal0 : alChk RuCS.LR L AL0 0 512 = true := ch7233al_0
theorem hal1 : alChk RuCS.LR L AL1 1 64 = true := ch7233al_1
theorem hal2 : alChk RuCS.LR L AL2 2 128 = true := ch7233al_2
theorem hal3 : alChk RuCS.LR L AL3 3 128 = true := ch7233al_3
theorem hal4 : alChk RuCS.LR L AL4 4 64 = true := ch7233al_4
theorem hal5 : alChk RuCS.LR L AL5 5 256 = true := ch7233al_5

theorem hch0 : ∀ a' < 512, elChk RuCS.LR RuCS.TR R Q AL0 EL0 0 (Nat.mul 32 (a' / 32)) 32 = true :=
  fun a' ha' => e0All (a' / 32) (by change a' / 32 < 16; omega)
theorem hch1 : ∀ a' < 64, elChk RuCS.LR RuCS.TR R Q AL1 EL1 1 (Nat.mul 32 (a' / 32)) 32 = true :=
  fun a' ha' => e1All (a' / 32) (by change a' / 32 < 2; omega)
theorem hch2 : ∀ a' < 128, elChk RuCS.LR RuCS.TR R Q AL2 EL2 2 (Nat.mul 32 (a' / 32)) 32 = true :=
  fun a' ha' => e2All (a' / 32) (by change a' / 32 < 4; omega)
theorem hch3 : ∀ a' < 128, elChk RuCS.LR RuCS.TR R Q AL3 EL3 3 (Nat.mul 32 (a' / 32)) 32 = true :=
  fun a' ha' => e3All (a' / 32) (by change a' / 32 < 4; omega)
theorem hch4 : ∀ a' < 64, elChk RuCS.LR RuCS.TR R Q AL4 EL4 4 (Nat.mul 32 (a' / 32)) 32 = true :=
  fun a' ha' => e4All (a' / 32) (by change a' / 32 < 2; omega)
theorem hch5 : ∀ a' < 256, elChk RuCS.LR RuCS.TR R Q AL5 EL5 5 (Nat.mul 32 (a' / 32)) 32 = true :=
  fun a' ha' => e5All (a' / 32) (by change a' / 32 < 8; omega)

theorem l0_of {a : Nat} (ha : a < 1920) :
    l0OK RuCS.LR RuCS.TR R L a = true ∧ l0kOK L a = true := by
  have h : allN 480 (fun d => l0OK RuCS.LR RuCS.TR R L (Nat.add (Nat.mul 480 (a / 480)) d)) =
      true := l0All (a / 480) (by change a / 480 < 4; omega)
  have h' : l0OK RuCS.LR RuCS.TR R L (Nat.add (Nat.mul 480 (a / 480)) (a % 480)) = true :=
    CFSG.KC.Misc.RuBase.allN_iff.1 h (a % 480) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 480 (a / 480)) (a % 480) = a := by
    change 480 * (a / 480) + a % 480 = a
    omega
  rw [e] at h'
  have hk : allN 1920 (fun i => l0kOK L i) = true := ch7233lk
  exact ⟨h', CFSG.KC.Misc.RuBase.allN_iff.1 hk a ha⟩

theorem bigZ_elt {a j : Nat} (ha : a < 1920) (hj : j < 128) {g₀ g₁ g₂ : Equiv.Perm (Fin 4060)}
    (P0 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 0) + a)) g₀)
    (P1 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 1) + j / 2)) g₁)
    (P2 : PRep 4060 12 (RuCS.TR (roff 4060 48720 (RuCS.LR 2) + j % 2)) g₂)
    (hg : g₀ * g₁ * g₂ ∈ ruP) : BigZ (g₀ * g₁ * g₂) := by
  have hf := ptR_y3 P0 P1 P2
  obtain ⟨hl0, hlk⟩ := l0_of ha
  have L0 := l0OK_sound hl0 hlk
  have eb := ebasisK
  refine ⟨fun hc h2 ho => ?_, fun hc => ?_, fun hc => ?_, fun hc => ?_, fun hn => ?_, fun hc => ?_⟩
  · by_cases hL : L (21 * a + 0) = 1
    · obtain ⟨rec, hr⟩ := alive hal0 hch0 ha hj hL
      rcases elOne_sound0 hr with hn | ho'
      · exact absurd hc (not_cent pE hf hn)
      · exact mem_of_orbC (ptR_QW (k := 10) (Or.inl rfl)).1 (ptR_QW (k := 10) (Or.inl rfl)).2
          pV32E eb.2.2.2.2.2.1 hg hf ho' h2 ho
    · obtain ⟨k, hk, r, hr, he, hn⟩ := L0.1 0 (by norm_num) hL
      exact absurd hc (cent_ne pE hj P0 P1 P2 hk hr he hn)
  · by_cases hL : L (21 * a + 1) = 1
    · obtain ⟨rec, hr⟩ := alive hal1 hch1 ha hj hL
      rcases elOne_sound1 hr with hn | ⟨m, -, hb⟩
      · exact absurd hc (not_cent p64 hf hn)
      · exact mem_of_mAp p64 eb.2.1 hg hf hb
    · obtain ⟨k, hk, r, hr, he, hn⟩ := L0.1 1 (by norm_num) hL
      exact absurd hc (cent_ne p64 hj P0 P1 P2 hk hr he hn)
  · by_cases hL : L (21 * a + 2) = 1
    · obtain ⟨rec, hr⟩ := alive hal2 hch2 ha hj hL
      rcases elOne_sound2 hr with hn | ⟨m, -, hb⟩
      · exact absurd hc (not_cent p3 hf hn)
      · exact mem_of_mAp p64 eb.2.1 hg hf hb
    · obtain ⟨k, hk, r, hr, he, hn⟩ := L0.1 2 (by norm_num) hL
      exact absurd hc (cent_ne p3 hj P0 P1 P2 hk hr he hn)
  · by_cases hL : L (21 * a + 3) = 1
    · obtain ⟨rec, hr⟩ := alive hal3 hch3 ha hj hL
      rcases elOne_sound3 hr with hn | ⟨h2c, hgc, hoc⟩
      · exact absurd hc (not_cent p16 hf hn)
      · exact ⟨pow_of_twoC hg hf h2c, cent_of_g16C hg hf hgc, fun h2 ho =>
          mem_of_orbC (ptR_QW (k := 12) (Or.inr (Or.inl rfl))).1
            (ptR_QW (k := 12) (Or.inr (Or.inl rfl))).2 pV32p eb.2.2.2.2.2.2 hg hf hoc h2 ho⟩
    · obtain ⟨k, hk, r, hr, he, hn⟩ := L0.1 3 (by norm_num) hL
      exact absurd hc (cent_ne p16 hj P0 P1 P2 hk hr he hn)
  · by_cases hL : L (21 * a + 5) = 1
    · obtain ⟨rec, hr⟩ := alive hal5 hch5 ha hj hL
      rcases elOne_sound5 hr with ⟨k, hk, p, hp, hne⟩ | h2c
      · exact absurd hn (not_norm hf hk hp hne)
      · exact pow_of_twoC hg hf h2c
    · obtain ⟨k, hk, hw⟩ := L0.2 hL
      exact absurd hn (norm_ne hj P0 P1 P2 hk hw)
  · by_cases hL : L (21 * a + 4) = 1
    · obtain ⟨rec, hr⟩ := alive hal4 hch4 ha hj hL
      rcases elOne_sound4 hr with hn | ⟨h2c, hoc⟩
      · exact absurd hc (not_cent p32 hf hn)
      · exact ⟨pow_of_twoC hg hf h2c, fun h2 ho =>
          mem_of_orbC (ptR_QW (k := 14) (Or.inr (Or.inr (Or.inl rfl)))).1
            (ptR_QW (k := 14) (Or.inr (Or.inr (Or.inl rfl)))).2 p32 eb.2.2.2.2.1 hg hf hoc h2 ho⟩
    · obtain ⟨k, hk, r, hr, he, hn⟩ := L0.1 4 (by norm_num) hL
      exact absurd hc (cent_ne p32 hj P0 P1 P2 hk hr he hn)

theorem bigZ_allK : ∀ g ∈ ruC, BigZ g := by
  intro g hg
  obtain ⟨a, ha, j, hj, g₀, g₁, g₂, P0, P1, P2, rfl⟩ := ruC_decomp hg
  exact bigZ_elt ha hj P0 P1 P2 (ruC_le hg)

end Glue

end CertificateChecks.KernelMisc.RuBigZ

end
